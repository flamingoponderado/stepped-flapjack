import SteppedFlapjack.CrepToLoopSteps.ScalarSequenceBound
import SteppedFlapjack.Concrete.WitnessLoopCode

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

def nestedLoopExample : CrepProgHOL 64 :=
  .seq (.while (.const 1) (.seq (.while (.const 0) .skip) (.break 0))) (.return [.const 7])

private theorem optimizedSkipSize : sizeOf (optimiseScalar (.skip : HolLoopProg 64)) = 2 := by decide +kernel
private theorem optimizedBreakSize : sizeOf (optimiseScalar (.break 0 : HolLoopProg 64)) = 2 := by decide +kernel
private theorem optimizedReturnSize : sizeOf (optimiseScalar
    (.seq (.assign 1 (.const (BitVec.ofNat 64 7))) (.seq (.return [1]) .skip) : HolLoopProg 64)) = 24 := by decide +kernel

/-- The concrete factor is computable from code and architecture. -/
example (arch : AsmArchitecture) :
    scalarProgramFactor (mkCtxtExact arch (makeVmapExact []) HolFiniteMapExact.empty 0) .ln nestedLoopExample = 16677 := by
  simp [nestedLoopExample,scalarProgramFactor,scalarNoWhile,optimizedSkipSize,optimizedBreakSize,compileHOLExact,compileExpHOLExact,compileExpsHOLExact,
    loopNestedSeqHOL,genTemps,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq]
  rw [optimizedReturnSize]

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
    let budget := scalarProgramFactor ctxt .ln computedConditionalExample * 9
    let code := compileHOLExact ctxt .ln computedConditionalExample
    ∃ post, evaluate (optimiseHOL code) {target with clock := target.clock+2*budget} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+2*budget} ≤
        sizeOf (optimiseScalar code)*(2*budget+1) := by
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
        {target with clock := target.clock+233478} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps (optimiseHOL (compileHOLExact ctxt .ln nestedLoopExample))
        {target with clock := target.clock+233478} ≤ 19845715 := by
  let crep := SteppedFlapjack.Concrete.crepStateFrom source SteppedFlapjack.Concrete.branchingHOL
  let target := SteppedFlapjack.Concrete.loopStateFrom arch source SteppedFlapjack.Concrete.branchingHOL
  let ctxt := SteppedFlapjack.Concrete.witnessLoopContext arch SteppedFlapjack.Concrete.branchingHOL
  have rel := SteppedFlapjack.Concrete.loopStateFrom_relations arch source SteppedFlapjack.Concrete.branchingHOL
  have codeLocals := SteppedFlapjack.Concrete.branching_loop_code_locals arch source
  have factor : scalarProgramFactor ctxt .ln nestedLoopExample = 16677 := by
    simp [ctxt,SteppedFlapjack.Concrete.witnessLoopContext,nestedLoopExample,scalarProgramFactor,scalarNoWhile,optimizedSkipSize,optimizedBreakSize,
      compileHOLExact,compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,genTemps,mkCtxtExact,
      makeVmapExact,HolFiniteMapExact.updateListEq]
    rw [optimizedReturnSize]
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
  have size : sizeOf (optimiseScalar (compileHOLExact ctxt .ln nestedLoopExample)) = 85 := by
    rw [codeEq]
    dsimp only [loopCode]
    decide +kernel
  obtain ⟨post,run,bound,_,_,_,_⟩ := scalarProgram_explicit nestedLoopExample nestedLoop_shape ctxt .ln
    crep (decClockCrepSemHOL crep).emptyLocals (some (.return [.word 7])) target 6
    (nestedLoop_run crep positive) (by rw [nestedLoop_steps crep positive]) (.return _)
    rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2
  refine ⟨post,?_,?_⟩
  · simpa [factor,resultToLoop,wlabWlocExact] using run
  · simpa [factor,size] using bound

end SteppedFlapjack.CrepToLoopSteps
