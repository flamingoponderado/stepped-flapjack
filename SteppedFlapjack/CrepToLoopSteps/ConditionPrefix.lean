import SteppedFlapjack.CrepToLoopSteps.BranchPrefix
import SteppedFlapjack.CrepToLoopSteps.ConditionSequence

/-! Bounded initialization and continuation for comparison loops. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- The while-and-continuation bound has a factor computed from compiled syntax,
without an existential expression in the factor. -/
theorem conditionWhileThenBranch_programBound {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ (.seq (.while condition body) tail) ctxt live
      (1 + (1 + sizeOf (compileHOLExact ctxt live (.while condition body))) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) + sizeOf (compileHOLExact ctxt live body)+3) + sizeOf (compileHOLExact ctxt live tail)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨code,value,next,outLive,extra,post,exprCompiled,compiled,he,hs,hm,hg,hc,hl,bound⟩ :=
    conditionWhileThenBranch_correct_with_steps condition conditionShape body tail bodyShape tailShape source sourceFinal result
      target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
  refine ⟨extra,post,he,hs,hm,hg,hc,hl,?_⟩
  have bodySize : sizeOf (branchConditionWhileBody ctxt live code value next body) ≤
      sizeOf (compileHOLExact ctxt live (.while condition body)) := by
    rw [compiled]
    simp_wf
    omega
  have codeEq : code = (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1 := by
    simpa using congrArg Prod.fst exprCompiled.symm
  rw [codeEq] at bound
  rw [codeEq] at bodySize
  have cost := Nat.mul_le_mul_right (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) + sizeOf (compileHOLExact ctxt live body)+3)
    (Nat.add_le_add_left bodySize 1)
  apply Nat.le_trans bound
  apply Nat.mul_le_mul_right
  omega

/-- Initialization, loop, and continuation compile with a fully discharged
source-step bound; no correctness hypothesis is required for a subprogram. -/
theorem branchConditionWhileBranch_programBound {width : Nat} [NeZero width] {σ : Type}
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ (.seq init (.seq (.while condition body) tail)) ctxt live
      (1 + sizeOf (compileHOLExact ctxt live init) +
        (1 + (1 + sizeOf (compileHOLExact ctxt live (.while condition body))) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) + sizeOf (compileHOLExact ctxt live body)+3) + sizeOf (compileHOLExact ctxt live tail))) :=
  branchPrefix_bound init (.seq (.while condition body) tail) initShape ctxt live _
    (conditionWhileThenBranch_programBound condition conditionShape body tail bodyShape tailShape ctxt live)

/-- The same compiled sequence lies in the selected RISC-V fragment. -/
theorem branchConditionWhileBranch_select {width : Nat} [NeZero width]
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSelectProgram (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) := by
  simpa only [compileHOLExact] using LoopSelectProgram.seq (compile_branchProgram_select initShape ctxt live)
    (conditionWhileThenBranch_select condition conditionShape body tail bodyShape tailShape ctxt live)


end SteppedFlapjack.CrepToLoopSteps
