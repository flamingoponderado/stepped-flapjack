import SteppedFlapjack.CrepToLoopSteps.ScalarSequenceBound
import SteppedFlapjack.Concrete.WitnessLoopCode

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

def nestedLoopExample : CrepProgHOL 64 :=
  .seq (.while (.const 1) (.seq (.while (.const 0) .skip) (.break 0))) (.return [.const 7])

/-- The concrete factor is computable from code and architecture. -/
example (arch : AsmArchitecture) :
    scalarLoopTreeFactor (mkCtxtExact arch (makeVmapExact []) HolFiniteMapExact.empty 0) .ln nestedLoopExample = 12532 := by
  simp [nestedLoopExample,scalarLoopTreeFactor,scalarNoWhile,compileHOLExact,compileExpHOLExact,compileExpsHOLExact,
    loopNestedSeqHOL,genTemps,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq]

/-- The recursive shape includes the reached inner loop and the outer break. -/
theorem nestedLoop_shape : ScalarLoopTree nestedLoopExample := by
  exact .seq (.while (.direct (.const 1)) (.seq (.while (.direct (.const 0)) (.branch .skip rfl)) (.branch (.break 0) rfl)))
    (.branch (.ret (.direct (.const 7))) rfl)

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
example : ScalarLoopTree (.dec 3 (.const 0) nestedLoopExample) :=
  .dec 3 (.const 0) nestedLoop_shape

/-- That declaration has a completed return on the same positive-clock states. -/
example {σ : Type} (state : CrepSemHOLState 64 σ) (positive : state.clock ≠ 0) :
    (evalCrepSemHOLProgExact state (.dec 3 (.const 0) nestedLoopExample)).1 =
      some (.return [.word 7]) := by
  rw [evalCrepSemHOLProgExact_dec_holShape]
  simp only [evalCrepSemHOLExp]
  have run := nestedLoop_run (CrepSemHOLState.setVar 3 (.word 0) state) (by simpa [CrepSemHOLState.setVar] using positive)
  simpa [CrepSemHOLState.setVar] using congrArg Prod.fst run

/-- Instantiation supplies a numeric target clock and optimized visit bound. -/
example {σ : Type} (arch : AsmArchitecture) (source : PanSemStateFiniteExact 64 σ)
    (positive : (SteppedFlapjack.Concrete.crepStateFrom source SteppedFlapjack.Concrete.branchingHOL).clock ≠ 0) :
    let target := SteppedFlapjack.Concrete.loopStateFrom arch source SteppedFlapjack.Concrete.branchingHOL
    let ctxt := SteppedFlapjack.Concrete.witnessLoopContext arch SteppedFlapjack.Concrete.branchingHOL
    ∃ post, evaluate (optimiseHOL (compileHOLExact ctxt .ln nestedLoopExample))
        {target with clock := target.clock+175448} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps (optimiseHOL (compileHOLExact ctxt .ln nestedLoopExample))
        {target with clock := target.clock+175448} ≤ 14913165 := by
  let crep := SteppedFlapjack.Concrete.crepStateFrom source SteppedFlapjack.Concrete.branchingHOL
  let target := SteppedFlapjack.Concrete.loopStateFrom arch source SteppedFlapjack.Concrete.branchingHOL
  let ctxt := SteppedFlapjack.Concrete.witnessLoopContext arch SteppedFlapjack.Concrete.branchingHOL
  have rel := SteppedFlapjack.Concrete.loopStateFrom_relations arch source SteppedFlapjack.Concrete.branchingHOL
  have codeLocals := SteppedFlapjack.Concrete.branching_loop_code_locals arch source
  have factor : scalarLoopTreeFactor ctxt .ln nestedLoopExample = 12532 := by
    simp [ctxt,SteppedFlapjack.Concrete.witnessLoopContext,nestedLoopExample,scalarLoopTreeFactor,scalarNoWhile,
      compileHOLExact,compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,genTemps,mkCtxtExact,
      makeVmapExact,HolFiniteMapExact.updateListEq]
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
  obtain ⟨post,run,bound,_,_,_,_⟩ := scalarLoopTree_explicit nestedLoopExample nestedLoop_shape ctxt .ln
    crep (decClockCrepSemHOL crep).emptyLocals (some (.return [.word 7])) target 6
    (nestedLoop_run crep positive) (by rw [nestedLoop_steps crep positive]) (.return _)
    rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2
  refine ⟨post,?_,?_⟩
  · simpa [factor,resultToLoop,wlabWlocExact] using run
  · simpa [factor,size] using bound

end SteppedFlapjack.CrepToLoopSteps
