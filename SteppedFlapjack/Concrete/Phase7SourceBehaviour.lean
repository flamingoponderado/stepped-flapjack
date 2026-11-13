import SteppedFlapjack.Concrete.Phase7SourceClock

/-! Connect original declarations to the source observational semantics. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

/-- A counted body return determines the original function declarations' behavior. -/
theorem functionOnly_body_semantics (state : PanSemStateFiniteExact 64 Unit) (start : MlS)
    (functions : List (FunDeclHOL 64)) (body : ProgHOL 64)
    (wellFormed : functions.all (fun f => f.params.all (fun p => isWfShapeExactHOL ([] : StructContextExact) p.2) &&
      isWfShapeExactHOL ([] : StructContextExact) f.returnShape) = true)
    (unique : ((functionsHOL (functions.map DeclHOL.function)).map Prod.fst).Nodup)
    (emptyCode : state.code = HolFiniteMapExact.empty) (emptyLocals : state.locals = HolFiniteMapExact.empty)
    (found : (functionsHOL (functions.map DeclHOL.function)).lookup start = some ([],body,.one))
    (clock : Nat) (final : PanSemStateFiniteExact 64 Unit) (word : BitVec 64)
    (run : let declared := {state with structs := [], code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (functions.map DeclHOL.function)).reverse)}
      ({declared with clock := clock} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState body =
        (some (.returned (.val (.word word))),final)) :
    semanticsDecls state start (functions.map DeclHOL.function) = .terminate .success final.ffi.ioEvents := by
  let declared : PanSemStateFiniteExact 64 Unit := {state with structs := [], code := (HolFiniteMapExact.empty.updateList
    (functionsHOL (functions.map DeclHOL.function)).reverse)}
  have lookupMap : declared.code.lookup start = some ([],body,.one) := by
    change FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL (functions.map DeclHOL.function)).reverse) start = _
    rwa [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
  have lookup : lookupCodeHOLFinite declared.code.lookup start [] = some (body,HolFiniteMapExact.empty,.one) := by
    apply SemInitSupport.lookup_init
    exact lookupMap
  have entry : callEntryStateHOLFinite {declared with clock := clock+1} HolFiniteMapExact.empty =
      {declared with clock := clock} := by
    simp [callEntryStateHOLFinite,declared,emptyLocals]
  change ({declared with clock := clock} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState body = _ at run
  have callRun : evaluateHOLFiniteState {declared with clock := clock+1} (.call none start []) =
      (some (.returned (.val (.word word))),emptyLocalsHOLFinite final) := by
    rw [evaluateHOLFiniteState_call]
    simp only [evalListHOLFinite,evalListHOLExact,lookup,show clock+1 ≠ 0 by omega,↓reduceIte,entry,run]
    simp [shapeOfHOLExact,shapeEqHOL]
  have semanticsEq : semanticsDecls state start (functions.map DeclHOL.function) = semantics declared start := by
    rw [source_function_declarations_semantics state start functions wellFormed,emptyCode,updateList_reverse_nodup _ unique]
  rw [semanticsEq]
  have h := source_semantics_of_return declared (emptyLocalsHOLFinite final) start (clock+1) (.val (.word word)) callRun
  simpa [emptyLocalsHOLFinite] using h

end SteppedFlapjack.Concrete
