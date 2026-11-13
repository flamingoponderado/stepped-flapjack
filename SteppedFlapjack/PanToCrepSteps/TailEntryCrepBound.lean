import SteppedFlapjack.PanToCrepSteps.TailEntrySteps
import SteppedFlapjack.PanToCrepSteps.BranchWhile
import SteppedFlapjack.CrepToLoopSteps.TailEntryLoop

/-! Quantitative Pancake-to-Crep bridge for a reached direct tail entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.PanSemStateFiniteExact SteppedFlapjack.CrepToLoopSteps

/-- A successful initializer and reached supported callee give a Crep entry
visit bound in terms of actual Pancake global-entry visits. The ordinary
frontend state and code relations are required at the callee entry. -/
theorem tailEntry_crep_bound {width : Nat} [NeZero width] {F : Type}
    (panInit : ProgHOL width) (name : MlString) (context : PanToCrepContextExact width)
    (calleeInit : ProgHOL width) (condition : ExpHOL width) (body tail : ProgHOL width)
    (calleeInitShape : BranchProgram context calleeInit) (conditionShape : ScalarExpression context condition)
    (bodyShape : BranchProgram context body) (tailShape : BranchProgram context tail)
    (pan panMiddle panPost : PanSemStateFiniteExact width F) (result : Option (PanSemResultExact width))
    (panLocals : HolFiniteMapExact MlString (ValueHOL width)) (returnShape : ShapeHOL)
    (crep crepMiddle : CrepSemHOLState width F) (crepInit : CrepProgHOL width)
    (crepInitShape : CrepToLoopSteps.BranchProgram crepInit)
    (panInitRun : pan.evaluateHOLFiniteState panInit = (none,panMiddle))
    (panLookup : lookupCodeHOLFinite panMiddle.code.lookup name [] =
      some (.seq calleeInit (.seq (.while condition body) tail),panLocals,returnShape))
    (panClock : panMiddle.clock ≠ 0)
    (panRun : (callEntryStateHOLFinite panMiddle panLocals).evaluateHOLFiniteState
      (.seq calleeInit (.seq (.while condition body) tail)) = (result,panPost))
    (nonerror : result ≠ some .error)
    (crepInitRun : evalCrepSemHOLProgExact crep crepInit = (none,crepMiddle))
    (crepFound : crepMiddle.code.lookup name = some ([],compileProgExactHOLW context
      (.seq calleeInit (.seq (.while condition body) tail))))
    (crepClock : crepMiddle.clock ≠ 0)
    (stateRel : panToCrepStateRelFiniteExact (callEntryStateHOLFinite panMiddle panLocals)
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}))
    (codeRel : codeRelExactHOLW context (callEntryStateHOLFinite panMiddle panLocals).code
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids (callEntryStateHOLFinite panMiddle panLocals).eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context (callEntryStateHOLFinite panMiddle panLocals).locals
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).locals)
    (localised : localisedProgHOL (.seq calleeInit (.seq (.while condition body) tail)) = true) :
    CrepSteps.steps (.seq crepInit (.call none name [])) crep ≤
      sizeOf crepInit + 2 +
        (3 + sizeOf (compileProgExactHOLW context calleeInit) + sizeOf (compileProgExactHOLW context body) +
          sizeOf (compileProgExactHOLW context tail)) * globalEntrySteps panInit name [] pan := by
  have calleeBound := branchWhileBranch_compiled_steps calleeInit condition body tail context calleeInitShape
    conditionShape bodyShape tailShape (callEntryStateHOLFinite panMiddle panLocals) panPost result
    (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []})
    panRun nonerror stateRel codeRel excpRel localsRel localised
  have initBound := CrepSteps.branchProgram_static crepInitShape crep
  have panCount : controlSteps (.seq calleeInit (.seq (.while condition body) tail))
      (callEntryStateHOLFinite panMiddle panLocals) ≤ globalEntrySteps panInit name [] pan := by
    rw [globalEntrySteps,controlSteps_seq panInit (.call none name []) pan,panInitRun]
    dsimp only
    rw [controlSteps_tailCall name [] panMiddle [] _ panLocals returnShape (by rfl) panLookup panClock]
    omega
  rw [CrepSteps.steps_seq,crepInitRun]
  simp only
  rw [CrepSteps.steps_call_tail name [] crepMiddle [] [] _ (by rfl) crepFound (by rfl) (by simp) crepClock]
  simp only [List.zip, List.zipWith] at *
  have scale := Nat.mul_le_mul_left
    (3 + sizeOf (compileProgExactHOLW context calleeInit) + sizeOf (compileProgExactHOLW context body) +
      sizeOf (compileProgExactHOLW context tail)) panCount
  omega

end SteppedFlapjack.PanToCrepSteps
