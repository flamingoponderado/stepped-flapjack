import SteppedFlapjack.Concrete.ScopePreservation
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

example : ScalarScopePresent ["x"]
    (setVarHOLFinite (ofString "x") (.val (.word 0)) (exactState branchingHOL)) := by
  have present : ScalarScopePresent [] (exactState branchingHOL) := ScalarScopePresent.empty _
  exact present.setVar "x" 0

example : ScalarScopeResult ["x"] none
    (setVarHOLFinite (ofString "x") (.val (.word 0))
      (setVarHOLFinite (ofString "x") (.val (.word 1)) (exactState branchingHOL))) := by
  let source := setVarHOLFinite (ofString "x") (.val (.word 1)) (exactState branchingHOL)
  have present : ScalarScopePresent ["x"] source := (ScalarScopePresent.empty _).setVar "x" 1
  have run : source.evaluateHOLFiniteState (progToHOL (.assign .local "x" (.const 0) : Prog (RiscV.Word 64))) =
      (none,setVarHOLFinite (ofString "x") (.val (.word 0)) source) := by
    simp [source,progToHOL,expToHOL,evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,lookupKvarHOLExact,
      setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,shapeOfHOLExact,shapeEqHOL]
  exact supported_scope_result (.assign "x" (by simp) (.const 0)) source _ none present run
end SteppedFlapjack.Concrete
