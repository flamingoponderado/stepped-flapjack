import SteppedFlapjack.Concrete.Phase7SourceClock

/-! Connect original declarations to the source observational semantics. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

/-- A declaration evaluation and returned entry determine source behavior. -/
theorem declaration_body_semantics (state declared : PanSemStateFiniteExact 64 Unit)
    (declarations : List (DeclHOL 64)) (start : MlS) (body : ProgHOL 64) (structs : StructContextExact)
    (names : decsStcnamesHOLExact [] declarations = some structs)
    (decs : @evaluateDeclsHOLFinite 64 Unit _ {state with structs := structs}
      (fun a => Classical.propDecidable (state.memaddrs a)) declarations = some declared)
    (emptyLocals : declared.locals = HolFiniteMapExact.empty)
    (found : declared.code.lookup start = some ([],body,.one))
    (clock : Nat) (final : PanSemStateFiniteExact 64 Unit) (word : BitVec 64)
    (run : ({declared with clock := clock} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState body =
      (some (.returned (.val (.word word))),final)) :
    semanticsDecls state start declarations = .terminate .success final.ffi.ioEvents := by
  have lookup : lookupCodeHOLFinite declared.code.lookup start [] = some (body,HolFiniteMapExact.empty,.one) := by
    apply SemInitSupport.lookup_init
    exact found
  have entry : callEntryStateHOLFinite {declared with clock := clock+1} HolFiniteMapExact.empty =
      {declared with clock := clock} := by
    simp [callEntryStateHOLFinite,emptyLocals]
  have callRun : evaluateHOLFiniteState {declared with clock := clock+1} (.call none start []) =
      (some (.returned (.val (.word word))),emptyLocalsHOLFinite final) := by
    rw [evaluateHOLFiniteState_call]
    simp only [evalListHOLFinite,evalListHOLExact,lookup,show clock+1 ≠ 0 by omega,↓reduceIte,entry,run]
    simp [shapeOfHOLExact,shapeEqHOL]
  have sem := source_semantics_of_return declared (emptyLocalsHOLFinite final) start (clock+1) (.val (.word word)) callRun
  unfold semanticsDecls
  rw [names]
  simp only
  rw [decs]
  simpa [emptyLocalsHOLFinite] using sem

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
  classical
  let declared : PanSemStateFiniteExact 64 Unit := {state with structs := [], code := (HolFiniteMapExact.empty.updateList
    (functionsHOL (functions.map DeclHOL.function)).reverse)}
  have names : decsStcnamesHOLExact [] (functions.map DeclHOL.function) = some [] := by
    clear wellFormed unique found run
    induction functions with
    | nil => rfl
    | cons f fs ih => simpa [decsStcnamesHOLExact] using ih
  have initialized := source_function_declarations_compiler_code {state with structs := []} functions
    (by simpa using emptyCode) (by simpa using wellFormed) unique
  have init : @evaluateDeclsHOLFinite 64 Unit _ {state with structs := []}
      (fun a => Classical.propDecidable (state.memaddrs a)) (functions.map DeclHOL.function) = some declared := by
    simpa [declared] using initialized
  have code : declared.code.lookup start = some ([],body,.one) := by
    change FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL (functions.map DeclHOL.function)).reverse) start = _
    rwa [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
  exact declaration_body_semantics state declared (functions.map DeclHOL.function) start body [] names init
    (by simpa [declared] using emptyLocals) code clock final word run

end SteppedFlapjack.Concrete
