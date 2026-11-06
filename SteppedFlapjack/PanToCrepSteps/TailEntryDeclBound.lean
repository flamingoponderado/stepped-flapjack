import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.PanToCrepSteps.DeclSteps

/-! Quantitative source-to-Crep bridge for a declaration-wrapped callee. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.PanSemStateFiniteExact SteppedFlapjack.CrepToLoopSteps

/-- A reached declaration-wrapped callee bounds the actual Crep entry visits
by the Pancake global-entry visits. -/
theorem tailEntry_decl_crep_bound {width : Nat} [NeZero width] {F : Type}
    (panInit : ProgHOL width) (callee : MlString) (context : PanToCrepContextExact width)
    (name : MlS) (initializer : ExpHOL width) (init : ProgHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (initializerShape : ScalarExpression context initializer)
    (initShape : BranchProgram (scalarDeclContext context name) init)
    (conditionShape : ScalarExpression (scalarDeclContext context name) condition)
    (bodyShape : BranchProgram (scalarDeclContext context name) body)
    (tailShape : BranchProgram (scalarDeclContext context name) tail)
    (pan panMiddle panPost : PanSemStateFiniteExact width F) (result : Option (PanSemResultExact width))
    (panLocals : HolFiniteMapExact MlString (ValueHOL width)) (returnShape : ShapeHOL)
    (crep crepMiddle : CrepSemHOLState width F) (crepInit : CrepProgHOL width)
    (crepInitShape : CrepToLoopSteps.BranchProgram crepInit)
    (panInitRun : pan.evaluateHOLFiniteState panInit = (none,panMiddle))
    (panLookup : lookupCodeHOLFinite panMiddle.code.lookup callee [] =
      some (.dec name .one initializer (.seq init (.seq (.while condition body) tail)),panLocals,returnShape))
    (panClock : panMiddle.clock ≠ 0)
    (panRun : (callEntryStateHOLFinite panMiddle panLocals).evaluateHOLFiniteState
      (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) = (result,panPost))
    (nonerror : result ≠ some .error)
    (crepInitRun : evalCrepSemHOLProgExact crep crepInit = (none,crepMiddle))
    (crepFound : crepMiddle.code.lookup callee = some ([],compileProgExactHOLW context
      (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))) )
    (crepClock : crepMiddle.clock ≠ 0)
    (stateRel : panToCrepStateRelFiniteExact (callEntryStateHOLFinite panMiddle panLocals)
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}))
    (codeRel : codeRelExactHOLW context (callEntryStateHOLFinite panMiddle panLocals).code
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids (callEntryStateHOLFinite panMiddle panLocals).eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context (callEntryStateHOLFinite panMiddle panLocals).locals
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).locals)
    (localised : localisedProgHOL (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) = true) :
    CrepSteps.steps (.seq crepInit (.call none callee [])) crep ≤
      sizeOf crepInit + 2 +
        (4 + sizeOf (compileProgExactHOLW (scalarDeclContext context name) init) +
          sizeOf (compileProgExactHOLW (scalarDeclContext context name) body) +
          sizeOf (compileProgExactHOLW (scalarDeclContext context name) tail)) *
        globalEntrySteps panInit callee [] pan := by
  have calleeBound := scalarDecl_loop_run_compiled_steps name initializer init condition body tail context initializerShape
    initShape conditionShape bodyShape tailShape (callEntryStateHOLFinite panMiddle panLocals) panPost result
    (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []})
    panRun nonerror stateRel codeRel excpRel localsRel localised
  have initBound := CrepSteps.branchProgram_static crepInitShape crep
  have panCount : controlSteps (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))
      (callEntryStateHOLFinite panMiddle panLocals) ≤ globalEntrySteps panInit callee [] pan := by
    simp only [globalEntrySteps,panInitRun]
    rw [tailEntrySteps_reached callee [] panMiddle [] _ panLocals returnShape (by rfl) panLookup panClock]
    omega
  rw [CrepSteps.steps_seq,crepInitRun]
  simp only
  rw [CrepSteps.steps_call_tail callee [] crepMiddle [] [] _ (by rfl) crepFound (by rfl) (by simp) crepClock]
  simp only [List.zip, List.zipWith] at *
  have scale := Nat.mul_le_mul_left
    (4 + sizeOf (compileProgExactHOLW (scalarDeclContext context name) init) +
      sizeOf (compileProgExactHOLW (scalarDeclContext context name) body) +
      sizeOf (compileProgExactHOLW (scalarDeclContext context name) tail)) panCount
  omega

/-- A reached declaration-wrapped callee bounds the actual Crep entry visits
by the Pancake global-entry visits. -/
theorem tailEntry_declWhile_crep_bound {width : Nat} [NeZero width] {F : Type}
    (panInit : ProgHOL width) (callee : MlString) (context : PanToCrepContextExact width)
    (name : MlS) (initializer : ExpHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (initializerShape : ScalarExpression context initializer)
    (conditionShape : ScalarExpression (scalarDeclContext context name) condition)
    (bodyShape : BranchProgram (scalarDeclContext context name) body)
    (tailShape : BranchProgram (scalarDeclContext context name) tail)
    (pan panMiddle panPost : PanSemStateFiniteExact width F) (result : Option (PanSemResultExact width))
    (panLocals : HolFiniteMapExact MlString (ValueHOL width)) (returnShape : ShapeHOL)
    (crep crepMiddle : CrepSemHOLState width F) (crepInit : CrepProgHOL width)
    (crepInitShape : CrepToLoopSteps.BranchProgram crepInit)
    (panInitRun : pan.evaluateHOLFiniteState panInit = (none,panMiddle))
    (panLookup : lookupCodeHOLFinite panMiddle.code.lookup callee [] =
      some (.dec name .one initializer (.seq (.while condition body) tail),panLocals,returnShape))
    (panClock : panMiddle.clock ≠ 0)
    (panRun : (callEntryStateHOLFinite panMiddle panLocals).evaluateHOLFiniteState
      (.dec name .one initializer (.seq (.while condition body) tail)) = (result,panPost))
    (nonerror : result ≠ some .error)
    (crepInitRun : evalCrepSemHOLProgExact crep crepInit = (none,crepMiddle))
    (crepFound : crepMiddle.code.lookup callee = some ([],compileProgExactHOLW context
      (.dec name .one initializer (.seq (.while condition body) tail))) )
    (crepClock : crepMiddle.clock ≠ 0)
    (stateRel : panToCrepStateRelFiniteExact (callEntryStateHOLFinite panMiddle panLocals)
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}))
    (codeRel : codeRelExactHOLW context (callEntryStateHOLFinite panMiddle panLocals).code
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids (callEntryStateHOLFinite panMiddle panLocals).eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context (callEntryStateHOLFinite panMiddle panLocals).locals
      (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).locals)
    (localised : localisedProgHOL (.dec name .one initializer (.seq (.while condition body) tail)) = true) :
    CrepSteps.steps (.seq crepInit (.call none callee [])) crep ≤
      sizeOf crepInit + 2 +
        (3 + sizeOf (compileProgExactHOLW (scalarDeclContext context name) body) +
          sizeOf (compileProgExactHOLW (scalarDeclContext context name) tail)) *
        globalEntrySteps panInit callee [] pan := by
  have calleeBound := scalarDecl_whileThenBranch_run_compiled_steps name initializer condition body tail context initializerShape
    conditionShape bodyShape tailShape (callEntryStateHOLFinite panMiddle panLocals) panPost result
    (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []})
    panRun nonerror stateRel codeRel excpRel localsRel localised
  have initBound := CrepSteps.branchProgram_static crepInitShape crep
  have panCount : controlSteps (.dec name .one initializer (.seq (.while condition body) tail))
      (callEntryStateHOLFinite panMiddle panLocals) ≤ globalEntrySteps panInit callee [] pan := by
    simp only [globalEntrySteps,panInitRun]
    rw [tailEntrySteps_reached callee [] panMiddle [] _ panLocals returnShape (by rfl) panLookup panClock]
    omega
  rw [CrepSteps.steps_seq,crepInitRun]
  simp only
  rw [CrepSteps.steps_call_tail callee [] crepMiddle [] [] _ (by rfl) crepFound (by rfl) (by simp) crepClock]
  simp only [List.zip, List.zipWith] at *
  have scale := Nat.mul_le_mul_left
    (3 + sizeOf (compileProgExactHOLW (scalarDeclContext context name) body) +
      sizeOf (compileProgExactHOLW (scalarDeclContext context name) tail)) panCount
  omega

end SteppedFlapjack.PanToCrepSteps
