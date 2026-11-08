import SteppedFlapjack.CrepToLoopSteps.ScalarSequenceBound
import SteppedFlapjack.Concrete.WitnessLoopCode

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

def nestedLoopExample : CrepProgHOL 64 :=
  .seq (.while (.const 1) (.seq (.while (.const 0) .skip) (.break 0))) (.return [.const 7])

/-- Optimized control weights do not depend on literal magnitude. -/
example (x : BitVec 64) :
    loopVisitWeight (optimiseScalar (.assign 1 (.const x) : HolLoopProg 64)) = 2 := by rfl

example (x : BitVec 64) :
    loopVisitWeight (optimiseScalar (.seq (.assign 1 (.const x)) (.return [1]) : HolLoopProg 64)) = 6 := by
  simp [optimiseScalar,scalarDepth,shrinkScalar,SteppedFlapjack.LoopLiveSteps.shrinkBranch,
    markAllHOL,loopVisitWeight,sptListInsert,sptInsert,sptLookup,sptDelete]

/-- The output-derived envelope computes to a concrete natural number. -/
example : scalarOutputEnvelope 3 = 901 := by decide +kernel

/-- The envelope evaluates for the nested loop's concrete output weight. -/
private theorem nestedLoopEnvelope : scalarOutputEnvelope 46 =
    85838975299478796137350471140065246905153223130317616185985232102213238409 := by
  decide +kernel

/-- The recursive shape includes the reached inner loop and the outer break. -/
theorem nestedLoop_shape : ScalarProgram nestedLoopExample := by
  exact .seq (.while (.direct (.const 1)) (.seq (.while (.direct (.const 0)) .skip) (.break 0)))
    (.ret (.direct (.const 7)))

/-- The example has a completed source run when its initial clock is positive. -/
theorem nestedLoop_run {σ : Type} (state : CrepSemHOLState 64 σ) (positive : state.clock ≠ 0) :
    evalCrepSemHOLProgExact state nestedLoopExample = (some (.return [.word 7]),(decClockCrepSemHOL state).emptyLocals) := by
  rw [nestedLoopExample,evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_while_holShape]
  simp [evalCrepSemHOLExp,positive,evalCrepSemHOLProgExact_seq_holShape,
    evalCrepSemHOLProgExact_while_holShape,evalCrepSemHOLProgExact_break,evalCrepSemHOLProgExact_return]
/-- The completed run consumes six Crep visits. -/
theorem nestedLoop_steps {σ : Type} (state : CrepSemHOLState 64 σ) (positive : state.clock ≠ 0) :
    CrepSteps.steps nestedLoopExample state = 6 := by
  rw [nestedLoopExample,CrepSteps.steps_seq,evalCrepSemHOLProgExact_while_holShape]
  simp [evalCrepSemHOLExp,positive,evalCrepSemHOLProgExact_seq_holShape,
    evalCrepSemHOLProgExact_while_holShape,evalCrepSemHOLProgExact_break,CrepSteps.steps_while,
    CrepSteps.steps_seq,CrepSteps.steps_leaf]

/-- A declaration may enclose the recursive loop tree. -/
example : ScalarProgram (.dec 3 (.const 0) nestedLoopExample) :=
  .dec 3 (.direct (.const 0)) nestedLoop_shape

/-- That declaration has a completed return on the same positive-clock states. -/
example {σ : Type} (state : CrepSemHOLState 64 σ) (positive : state.clock ≠ 0) :
    (evalCrepSemHOLProgExact state (.dec 3 (.const 0) nestedLoopExample)).1 =
      some (.return [.word 7]) := by
  rw [evalCrepSemHOLProgExact_dec_holShape]
  simp only [evalCrepSemHOLExp]
  have run := nestedLoop_run (CrepSemHOLState.setVar 3 (.word 0) state) (by simpa [CrepSemHOLState.setVar] using positive)
  simpa [CrepSemHOLState.setVar] using congrArg Prod.fst run

/-- A computed initializer and a conditional can both enclose a nested loop. -/
def computedConditionalExample : CrepProgHOL 64 :=
  .dec 3 (.cmp .equal (.const 1) (.const 1)) (.ite (.const 1) nestedLoopExample .skip)

theorem computedConditional_shape : ScalarProgram computedConditionalExample :=
  .dec 3 (.cmp .equal (.direct (.const 1)) (.direct (.const 1)))
    (.ite (.direct (.const 1)) nestedLoop_shape .skip)

theorem computedConditional_run {σ : Type} (state : CrepSemHOLState 64 σ) (positive : state.clock ≠ 0) :
    (evalCrepSemHOLProgExact state computedConditionalExample).1 = some (.return [.word 7]) := by
  rw [computedConditionalExample,evalCrepSemHOLProgExact_dec_holShape]
  simp [evalCrepSemHOLExp,evalCrepSemHOLProgExact_ite_holShape,nestedLoop_run,
    positive]

theorem computedConditional_steps {σ : Type} (state : CrepSemHOLState 64 σ) (positive : state.clock ≠ 0) :
    CrepSteps.steps computedConditionalExample state = 8 := by
  rw [computedConditionalExample,CrepSteps.steps_dec]
  simp [evalCrepSemHOLExp,CrepSteps.steps_ite]
  rw [nestedLoop_steps _ (by simpa [CrepSemHOLState.setVar] using positive)]

/-- The computed initializer and conditional both execute under an explicit bound. -/
example {σ : Type} (arch : AsmArchitecture) (source : PanSemStateFiniteExact 64 σ)
    (positive : (SteppedFlapjack.Concrete.crepStateFrom source SteppedFlapjack.Concrete.branchingHOL).clock ≠ 0) :
    let target := SteppedFlapjack.Concrete.loopStateFrom arch source SteppedFlapjack.Concrete.branchingHOL
    let ctxt := SteppedFlapjack.Concrete.witnessLoopContext arch SteppedFlapjack.Concrete.branchingHOL
    let code := compileHOLExact ctxt .ln computedConditionalExample
    let budget := scalarOutputEnvelope (loopVisitWeight (optimiseHOL code)) * 9
    ∃ post, evaluate (optimiseHOL code) {target with clock := target.clock+2*budget} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+2*budget} ≤
        loopVisitWeight (optimiseHOL code)*(2*budget+1) := by
  let crep := SteppedFlapjack.Concrete.crepStateFrom source SteppedFlapjack.Concrete.branchingHOL
  let target := SteppedFlapjack.Concrete.loopStateFrom arch source SteppedFlapjack.Concrete.branchingHOL
  let ctxt := SteppedFlapjack.Concrete.witnessLoopContext arch SteppedFlapjack.Concrete.branchingHOL
  have rel := SteppedFlapjack.Concrete.loopStateFrom_relations arch source SteppedFlapjack.Concrete.branchingHOL
  have codeLocals := SteppedFlapjack.Concrete.branching_loop_code_locals arch source
  rcases h : evalCrepSemHOLProgExact crep computedConditionalExample with ⟨result,final⟩
  have resultEq := computedConditional_run crep positive
  rw [h] at resultEq
  simp only at resultEq
  subst result
  obtain ⟨post,run,bound,_,_,_,_⟩ := scalarProgram_explicit computedConditionalExample computedConditional_shape ctxt .ln
    crep final (some (.return [.word 7])) target 8 h
    (by rw [computedConditional_steps crep positive]) (.return _)
    rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2
  exact ⟨post,by simpa [resultToLoop,wlabWlocExact] using run,by simpa using bound⟩

/-- Instantiation supplies a numeric target clock and optimized visit bound. -/
example {σ : Type} (arch : AsmArchitecture) (source : PanSemStateFiniteExact 64 σ)
    (positive : (SteppedFlapjack.Concrete.crepStateFrom source SteppedFlapjack.Concrete.branchingHOL).clock ≠ 0) :
    let target := SteppedFlapjack.Concrete.loopStateFrom arch source SteppedFlapjack.Concrete.branchingHOL
    let ctxt := SteppedFlapjack.Concrete.witnessLoopContext arch SteppedFlapjack.Concrete.branchingHOL
    ∃ post, evaluate (optimiseHOL (compileHOLExact ctxt .ln nestedLoopExample))
        {target with clock := target.clock+1201745654192703145922906595960913456672145123824446626603793249430985337726} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps (optimiseHOL (compileHOLExact ctxt .ln nestedLoopExample))
        {target with clock := target.clock+1201745654192703145922906595960913456672145123824446626603793249430985337726} ≤ 55280300092864344712453703414202019006918675695924544823774489473825325535442 := by
  let crep := SteppedFlapjack.Concrete.crepStateFrom source SteppedFlapjack.Concrete.branchingHOL
  let target := SteppedFlapjack.Concrete.loopStateFrom arch source SteppedFlapjack.Concrete.branchingHOL
  let ctxt := SteppedFlapjack.Concrete.witnessLoopContext arch SteppedFlapjack.Concrete.branchingHOL
  have rel := SteppedFlapjack.Concrete.loopStateFrom_relations arch source SteppedFlapjack.Concrete.branchingHOL
  have codeLocals := SteppedFlapjack.Concrete.branching_loop_code_locals arch source
  let loopCode : HolLoopProg 64 := .seq
    (.loop .ln (.seq (.assign 1 (.const 1)) (.seq
      (.ite .notEqual 1 (.imm 0)
        (.seq (.seq (.loop .ln (.seq (.assign 1 (.const 0)) (.seq
          (.ite .notEqual 1 (.imm 0) (.seq .skip (.continue 0)) (.break 0) .ln) .skip)) .ln)
          (.break 0)) (.continue 0)) (.break 0) .ln) .skip)) .ln)
    (.seq (.assign 1 (.const 7)) (.seq (.return [1]) .skip))
  have codeEq : compileHOLExact ctxt .ln nestedLoopExample = loopCode := by
    simp [ctxt,SteppedFlapjack.Concrete.witnessLoopContext,nestedLoopExample,loopCode,compileHOLExact,
      compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,genTemps,mkCtxtExact,makeVmapExact,
      HolFiniteMapExact.updateListEq]
  have size : loopVisitWeight (optimiseScalar (compileHOLExact ctxt .ln nestedLoopExample)) = 46 := by
    rw [codeEq]
    dsimp only [loopCode]
    decide +kernel
  have actualSize : loopVisitWeight (optimiseHOL (compileHOLExact ctxt .ln nestedLoopExample)) = 46 := by
    rw [← optimiseScalar_eq (compile_scalar_program nestedLoop_shape ctxt .ln)]
    exact size
  obtain ⟨post,run,bound,_,_,_,_⟩ := scalarProgram_explicit nestedLoopExample nestedLoop_shape ctxt .ln
    crep (decClockCrepSemHOL crep).emptyLocals (some (.return [.word 7])) target 6
    (nestedLoop_run crep positive) (by rw [nestedLoop_steps crep positive]) (.return _)
    rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2
  refine ⟨post,?_,?_⟩
  · simpa [actualSize,nestedLoopEnvelope,resultToLoop,wlabWlocExact] using run
  · simpa [actualSize,nestedLoopEnvelope] using bound

end SteppedFlapjack.CrepToLoopSteps
