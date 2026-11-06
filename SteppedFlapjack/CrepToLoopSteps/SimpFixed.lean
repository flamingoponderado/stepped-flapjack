import SteppedFlapjack.CrepToLoopSteps.WordSimpSequence
import Flapjack.Pancake.CrepArith
import SteppedFlapjack.LoopLiveSteps.FrontendMember
import SteppedFlapjack.LoopLiveSteps.Consumption
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.BackendReady

/-! The supported Crep frontend fragment is unchanged by Crep simplification. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopToWord Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Every direct expression is a fixed point of the actual Crep simplifier. -/
theorem directExpression_simp_fixed {width : Nat} [NeZero width]
    {e : CrepExpHOL width} (shape : DirectExpression e) : crepSimpExpHOL e = e := by
  induction shape <;> simp_all [crepSimpExpHOL]

/-- Comparisons of direct expressions are also fixed. -/
theorem branchCondition_simp_fixed {width : Nat} [NeZero width]
    {e : CrepExpHOL width} (shape : BranchCondition e) : crepSimpExpHOL e = e := by
  cases shape with
  | direct h => exact directExpression_simp_fixed h
  | cmp op ha hb => simp [crepSimpExpHOL,directExpression_simp_fixed ha,directExpression_simp_fixed hb]

/-- The expression-program fragment is unchanged by Crep simplification. -/
theorem exprProgram_simp_fixed {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : ExprProgram p) : crepSimpProgHOL p = p := by
  induction shape with
  | leaf h => cases h <;> simp [crepSimpProgHOL]
  | returnNil => simp [crepSimpProgHOL]
  | returnOne h => simp [crepSimpProgHOL,directExpression_simp_fixed h]
  | assign name h => simp [crepSimpProgHOL,directExpression_simp_fixed h]
  | storeGlob name h => simp [crepSimpProgHOL,directExpression_simp_fixed h]
  | store hd hs => simp [crepSimpProgHOL,directExpression_simp_fixed hd,directExpression_simp_fixed hs]
  | seq ha hb iha ihb => simp [crepSimpProgHOL,iha,ihb]

/-- Declarations, sequences and branches in the supported fragment are fixed. -/
theorem branchProgram_simp_fixed {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : BranchProgram p) : crepSimpProgHOL p = p := by
  induction shape with
  | expr h => exact exprProgram_simp_fixed h
  | dec he hb ih => simp [crepSimpProgHOL,directExpression_simp_fixed he,ih]
  | seq ha hb iha ihb => simp [crepSimpProgHOL,iha,ihb]
  | ite hc ha hb iha ihb => simp [crepSimpProgHOL,directExpression_simp_fixed hc,iha,ihb]

/-- The actual simplifier leaves the complete supported Crep loop shape intact. -/
theorem branchConditionWhileBranch_simp_fixed {width : Nat} [NeZero width]
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail) :
    crepSimpProgHOL (.seq init (.seq (.while condition body) tail)) =
      .seq init (.seq (.while condition body) tail) := by
  simp [crepSimpProgHOL,branchProgram_simp_fixed initShape,branchCondition_simp_fixed conditionShape,
    branchProgram_simp_fixed bodyShape,branchProgram_simp_fixed tailShape]

/-- The actual Crep and Loop list compilers put the supported zero-argument
function's optimized, unsimplified Loop body into their Word output. -/
theorem supported_crepToWord_member {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (code : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (name : Basis.Pure.MlString.MlString)
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (member : (name,[],.seq init (.seq (.while condition body) tail)) ∈ code) :
    let p := .seq init (.seq (.while condition body) tail)
    let loop := optimiseHOL (compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable code) [] p)
    ∃ index, let location := index + firstLoopName
      let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
      (location,1,(LoopToWord.compHOL ctxt loop (location,2)).1) ∈
        loopToWordCompileHOL (compileProgHOLExact arch code) ∧
      SteppedFlapjack.LoopToWordSteps.LoopSequenceSource loop := by
  have fixed := branchConditionWhileBranch_simp_fixed init initShape condition conditionShape body tail bodyShape tailShape
  obtain ⟨index,h⟩ := LoopLiveSteps.crepToWord_zeroArg_member arch code name _ member
  rw [fixed] at h
  refine ⟨index,h,?_⟩
  apply LoopLiveSteps.optimise_sequence
  unfold compFuncHOLExact
  exact branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape _ _

/-- A completed supported Crep run has a bounded execution of the exact
simplify/compile/optimize pipeline, measured against Crep source visits. -/
theorem supported_optimised_loop_bound {F : Type}
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourcePost : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F)
    (run : evalCrepSemHOLProgExact source (.seq init (.seq (.while condition body) tail)) = (result,sourcePost))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let p := .seq init (.seq (.while condition body) tail)
    let loop := compileHOLExact ctxt live (crepSimpProgHOL p)
    let factor := 1 + sizeOf (compileHOLExact ctxt live init) +
      (1 + (1 + sizeOf (compileHOLExact ctxt live (.while condition body))) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
          sizeOf (compileHOLExact ctxt live body)+3) + sizeOf (compileHOLExact ctxt live tail))
    ∃ extra targetPost,
      LoopSemStateFiniteExact.evaluate (optimiseHOL loop) {target with clock := target.clock+extra} =
        (resultToLoop result,targetPost) ∧
      crepToLoopStateRelExact sourcePost targetPost ∧
      LoopSteps.steps (optimiseHOL loop) {target with clock := target.clock+extra} ≤
        sizeOf (optimiseHOL loop) * (2 * (factor * (CrepSteps.steps p source+1)) + 1) := by
  have fixed := branchConditionWhileBranch_simp_fixed init initShape condition conditionShape body tail bodyShape tailShape
  simp only [fixed]
  obtain ⟨extra,post,loopRun,postRel,_,_,_,_,bound⟩ :=
    branchConditionWhileBranch_programBound init initShape condition conditionShape body tail bodyShape tailShape ctxt live
      source sourcePost result target run (completeCrep_nonerror complete) stateRel memRel globalsRel codeRel localsRel
  have shape := branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape ctxt live
  obtain ⟨optRun,_,optBound⟩ := LoopLiveSteps.optimise_complete_source_steps shape
    {target with clock := target.clock+extra} post (resultToLoop result) loopRun (completeCrep_loop complete)
  exact ⟨extra,post,optRun,postRel,optBound.trans (Nat.mul_le_mul_left _ (by omega))⟩

end SteppedFlapjack.CrepToLoopSteps
