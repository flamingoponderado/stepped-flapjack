import SteppedFlapjack.Concrete.FrontendState
import Flapjack.Pancake.CrepInline.InlineRouteBridge

/-! Kernel-checked frontend compiler outputs for the concrete witnesses. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

macro "simp_crep_code" : tactic => `(tactic| simp [compileToCrepExactHOLW,functionsHOL,compFuncExactHOLW,crepVarsHOL,
    compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,
    branchingHOL,countdownHOL,countdownBodyHOL,fpermHOL,compileProgExactHOL,compileExpExactHOL,
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

set_option linter.unusedSimpArgs false in
/-- The complete generated Crep function list for any countdown constant. -/
theorem countdown_crep_code (n : Nat) : crepPrograms (countdownHOL n) =
    [(ofString "main",[],.seq .skip (.call none (entryName (countdownHOL n)) [])),
     (entryName (countdownHOL n),[],.dec 1 (.const (BitVec.ofNat 64 n))
       (.seq .skip (.seq
         (.while (.var 1) (.dec 2 (.op .sub [.var 1,.const 1])
           (.seq (.assign 1 (.var 2)) .skip)))
         (.return [.const 0]))))] := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp_crep_code

end SteppedFlapjack.Concrete
