import SteppedFlapjack.CrepToLoopSteps.ConditionShape
import SteppedFlapjack.LoopToWordSteps.WordSimpLoop

/-! Derive WordSimp-ready Loop branches from actual Crep compilation. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

theorem compile_exprProgram_loopBranch {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : ExprProgram p)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopBranch (compileHOLExact ctxt live p) := by
  induction shape with
  | leaf leaf =>
    cases leaf <;> simp only [compileHOLExact] <;> constructor
  | returnNil =>
    simp only [compileHOLExact,compileExpsHOLExact,genTemps,List.nil_append]
    exact .seq (.ret _) (.skip)
  | returnOne expr =>
    obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
    simp [compileHOLExact,compileExpsHOLExact,h,genTemps,loopNestedSeqHOL]
    exact .seq (.assign _ _) (.seq (.ret _) (.skip))
  | assign name expr =>
    simp only [compileHOLExact]
    cases ctxt.vars.lookup name with
    | none => exact .skip
    | some mapped =>
      obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
      simp only [h,List.nil_append,loopNestedSeqHOL]
      exact .seq (.assign _ _) (.skip)
  | storeGlob name expr =>
    obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    exact .seq (.setGlobal _ _) (.skip)
  | store dst src =>
    obtain ⟨vd,hd⟩ := directExpression_noCode dst ctxt (ctxt.vmax + 1) live
    obtain ⟨vs,hs⟩ := directExpression_noCode src ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,hd,hs,List.nil_append,loopNestedSeqHOL]
    exact .seq (.assign _ _) (.seq (.store _ _) (.skip))
  | seq ha hb iha ihb => simpa only [compileHOLExact] using LoopBranch.seq iha ihb


theorem compile_branchProgram_loopBranch {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : BranchProgram p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopBranch (compileHOLExact ctxt live p) := by
  induction shape generalizing ctxt live with
  | expr shape => exact compile_exprProgram_loopBranch shape ctxt live
  | @dec name e body he hb ih =>
    obtain ⟨value,h⟩ := directExpression_noCode he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,h,loopNestedSeqHOL]
    exact .seq (.skip) (.seq (.assign _ _) (ih _ _))
  | seq ha hb iha ihb => simpa only [compileHOLExact] using LoopBranch.seq (iha ctxt live) (ihb ctxt live)
  | @ite cond a b hcond ha hb iha ihb =>
    obtain ⟨value,h⟩ := directExpression_noCode hcond ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    exact .seq (.assign _ _) (.seq (.ite _ _ _ _ (iha ctxt live) (ihb ctxt live)) (.skip))


/-- The compiler-generated condition prefix and body form a Loop branch. -/
theorem branchConditionWhile_loopBranch {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (conditionShape : BranchCondition condition)
    (body : CrepProgHOL width) (bodyShape : BranchProgram body)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    ∃ code value next outLive,
      compileExpHOLExact ctxt (ctxt.vmax+1) live condition = (code,value,next,outLive) ∧
      compileHOLExact ctxt live (.while condition body) =
        .loop live (branchConditionWhileBody ctxt live code value next body) live ∧
      LoopBranch (branchConditionWhileBody ctxt live code value next body) := by
  obtain ⟨code,value,next,outLive,compiled,_,_⟩ :=
    condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  have hprefix : ∀ p ∈ code, LoopBranch p := by
    cases conditionShape with
    | direct h =>
      obtain ⟨v,hv⟩ := directExpression_noCode h ctxt (ctxt.vmax+1) live
      rw [hv] at compiled
      cases compiled
      simp
    | @cmp op a b ha hb =>
      obtain ⟨va,ca⟩ := directExpression_noCode ha ctxt (ctxt.vmax+1) live
      obtain ⟨vb,cb⟩ := directExpression_noCode hb ctxt (ctxt.vmax+1) live
      have actual := compiled
      simp only [compileExpHOLExact,ca,cb,progIfHOLExact,List.nil_append] at actual
      cases actual
      intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact .assign _ _
      · exact .assign _ _
      · exact .ite _ _ _ _ (.assign _ _) (.assign _ _)
  have nested : ∀ code : List (HolLoopProg width), (∀ p ∈ code, LoopBranch p) → LoopBranch (loopNestedSeqHOL code) := by
    intro xs hx
    induction xs with
    | nil => exact .skip
    | cons p xs ih =>
      simp only [loopNestedSeqHOL]
      exact .seq (hx p (by simp)) (ih (by intro q hq; exact hx q (by simp [hq])))
  refine ⟨code,value,next,outLive,compiled,?_,?_⟩
  · simp only [compileHOLExact,compiled,branchConditionWhileBody]
  · apply nested
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact hprefix p h
    · exact .assign _ _
    · exact .ite _ _ _ _ (.seq (compile_branchProgram_loopBranch bodyShape ctxt live) (.continue 0)) (.break 0)

end SteppedFlapjack.CrepToLoopSteps
