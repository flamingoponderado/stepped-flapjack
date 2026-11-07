import SteppedFlapjack.Concrete.FrontendState
import Flapjack.Pancake.CrepInline.InlineRouteBridge

/-! Kernel-checked frontend compiler outputs for the concrete witnesses. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

macro "simp_crep_code" : tactic => `(tactic| simp [compileToCrepExactHOLW,functionsHOL,compFuncExactHOLW,crepVarsHOL,
    compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,
    branchingHOL,countdownHOL,countdownBodyHOL,naturalCountdownHOL,naturalCountdown,
    progToHOL,expToHOL,shapeToHOL,countdownBody,fpermHOL,compileProgExactHOL,compileExpExactHOL,
    compileExpExactHOLList,compileExpExactHOLW,compileIfExactHOLW,compileReturnExactHOLW,
    compileWhileExactHOLW,compileDecExactHOLW,compileLocalAssignExactHOLW,nestedDecsHOL,
    panToCrepMakeVmapHOLExact,mkCtxtExactHOL,entryName,FUPDATE,cexpHeads,
    distinctListsHol,crepExpVarsW,crepExpOfHOL,crepNestedSeqHOL,crepExpVars,crepExpVars.crepExpVarsList])

set_option linter.unusedSimpArgs false in
/-- The complete generated Crep function list for the comparison witness. -/
theorem branching_crep_code : crepPrograms branchingHOL =
    [(ofString "main",[],.seq .skip (.call none (entryName branchingHOL) [])),
     (entryName branchingHOL,[],.ite (.cmp .lower (.const 0) (.const 1))
       (.return [.const 7]) (.return [.const 9]))] := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp_crep_code

/-- The two generated countdown bodies differ only in the source skip prefix. -/
def countdownCrepBody (x : BitVec 64) : CrepProgHOL 64 :=
  .dec 1 (.const x) (.seq .skip (.seq
    (.while (.var 1) (.dec 2 (.op .sub [.var 1,.const 1])
      (.seq (.assign 1 (.var 2)) .skip))) (.return [.const 0])))

def naturalCountdownCrepBody (x : BitVec 64) : CrepProgHOL 64 :=
  .dec 1 (.const x) (.seq (.while (.var 1) (.dec 2 (.op .sub [.var 1,.const 1])
    (.seq (.assign 1 (.var 2)) .skip))) (.return [.const 0]))

set_option linter.auxLemma false in
/-- Code sizes are closed forms in the encoded countdown word. -/
theorem countdownCrepBody_sizes (x : BitVec 64) :
    sizeOf (countdownCrepBody x) = x.toNat + 38 ∧
    sizeOf (naturalCountdownCrepBody x) = x.toNat + 36 := by
  constructor <;> cases x with
  | ofFin f =>
    cases f with
    | mk val bound =>
      simp only [countdownCrepBody,naturalCountdownCrepBody,sizeOf,CrepProgHOL._sizeOf_1,
        CrepExpHOL._sizeOf_1,BitVec._sizeOf_1,Fin._sizeOf_1,List._sizeOf_1,BinOp._sizeOf_1,
        Nat.reduceAdd,default.sizeOf,BitVec.toNat]
      clear bound
      norm_num
      have literalOne : (1 : BitVec 64).toNat = 1 := by decide
      have literalZero : (0 : BitVec 64).toNat = 0 := by decide
      rw [literalOne, literalZero]
      omega

set_option linter.unusedSimpArgs false in
/-- The complete generated Crep function list for any countdown constant. -/
theorem countdown_crep_code (n : Nat) : crepPrograms (countdownHOL n) =
    [(ofString "main",[],.seq .skip (.call none (entryName (countdownHOL n)) [])),
     (entryName (countdownHOL n),[],countdownCrepBody (BitVec.ofNat 64 n))] := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp only [countdownCrepBody]
  simp_crep_code

set_option linter.unusedSimpArgs false in
/-- The complete generated Crep function list for the natural countdown. -/
theorem natural_countdown_crep_code (n : Nat) : crepPrograms (naturalCountdownHOL n) =
    [(ofString "main",[],.seq .skip (.call none (entryName (naturalCountdownHOL n)) [])),
     (entryName (naturalCountdownHOL n),[],naturalCountdownCrepBody (BitVec.ofNat 64 n))] := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp only [naturalCountdownCrepBody]
  simp_crep_code

end SteppedFlapjack.Concrete
