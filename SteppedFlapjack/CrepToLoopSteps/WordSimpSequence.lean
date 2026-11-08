import SteppedFlapjack.CrepToLoopSteps.WordSimpShape
import SteppedFlapjack.LoopToWordSteps.WordSimpSequence

/-! Crep initialization, loop and continuation produce WordSimp-ready code. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps

/-- The exact compiler emits the Loop sequence supported by the full WordSimp
shape proof, including generated comparison evaluation. -/
theorem branchConditionWhileBranch_wordSimpShape {width : Nat} [NeZero width]
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSequenceSource (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) := by
  obtain ⟨code,value,next,outLive,compiled,loopCompiled,loopBody⟩ :=
    branchConditionWhile_loopBranch condition conditionShape body bodyShape ctxt live
  simp only [compileHOLExact,loopCompiled]
  exact .seq (.branch (compile_branchProgram_loopBranch initShape ctxt live))
    (.seq (.loop live live loopBody) (.branch (compile_branchProgram_loopBranch tailShape ctxt live)))

/-- The actual Loop-to-Word and WordSimp output can enter the existing
instruction-selection theorem with no generated-program shape assumption. -/
theorem branchConditionWhileBranch_wordSimpProgram {width : Nat} [NeZero width]
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (wordCtxt : Spt Nat) (labels : Nat × Nat) :
    WordInstSteps.Program (Flapjack.Compiler.Backend.WordSimp.compileExp
      (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1) :=
  loopSequenceSource_wordSimp_program
    (branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape ctxt live)
    wordCtxt labels

end SteppedFlapjack.CrepToLoopSteps
