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

/-- The original declarations exhibit the same successful return and event
trace as a supported body run in the source fixture. -/
theorem supported_body_semantics (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (n : Nat) (final : PanSemStateFiniteExact 64 Unit) (word : BitVec 64)
    (run : (clockedFixtureSource program n).evaluateHOLFiniteState (progToHOL program) =
      (some (.returned (.val (.word word))),final)) :
    semanticsDecls {sourceTemplate with clock := 0} (ofString "main") (declarations (progToHOL program)) =
      .terminate .success final.ffi.ioEvents := by
  let body := progToHOL program
  let src := clockedFixtureSource program n
  let functions : List (FunDeclHOL 64) := [⟨ofString "main",false,false,[],body,.one⟩]
  let declared : PanSemStateFiniteExact 64 Unit := {sourceTemplate with code := sourceTemplate.code.update (ofString "main",([],body,.one))}
  have bodyRun := supported_code_irrel supported src declared.code
  rw [run] at bodyRun
  change ({src with code := declared.code} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState body =
    (some (.returned (.val (.word word))),{final with code := declared.code}) at bodyRun
  have result := functionOnly_body_semantics {sourceTemplate with clock := 0} (ofString "main") functions body
    (by simp [functions,isWfShapeExactHOL])
    (by simp [functions,functionsHOL]) rfl rfl
    (by simp [functions,functionsHOL]) n {final with code := declared.code} word
    (by simpa [functions,functionsHOL,declared,src,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate,
      HolFiniteMapExact.updateList,HolFiniteMapExact.update,FUPDATE_LIST,FUPDATE] using bodyRun)
  simpa [functions,declarations,singleEntryProgram] using result
/-- A counted supported source return determines the declaration behavior
and relates its events to the executable result. -/
theorem supported_counted_semantics (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (fuel count n : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (word : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL program)).structs []
      (executableState (progToHOL program)).baseAddress (executableState (progToHOL program)).topAddress
      panSemBitVec64BytesInWord fuel (executableState (progToHOL program)).locals
      (executableState (progToHOL program)).globals (executableState (progToHOL program)).memory
      (executableState (progToHOL program)).ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL program)))) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count)) (countBound : count ≤ n) :
    ∃ events, semanticsDecls {sourceTemplate with clock := 0} (ofString "main") (declarations (progToHOL program)) =
      .terminate .success events ∧ FfiEventListRel postFfi.ioEvents events := by
  let source := clockedFixtureSource program n
  let production := clockedFixtureProduction program n
  let _ : DecidablePred source.memaddrs := by
    change DecidablePred ordinaryAddress
    infer_instance
  obtain ⟨rel,ranged,words⟩ := clockedFixture_premises program n
  have run' : evalPanValueFfiProgSteps context primitive handler production.structs [] production.baseAddress
      production.topAddress panSemBitVec64BytesInWord fuel production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count) := by
    simpa [production,clockedFixtureProduction,panSemBitVec64MemoryAccess] using run
  obtain ⟨holResult,final,sourceRun,outcome,_,_⟩ := supported_counted_source supported.1 production source
    rel ranged words supported.2 context primitive handler [] fuel count
    (.returned postLocals postGlobals postMemory postFfi [.word word]) run' countBound
  cases outcome with
  | returned l g m f value st finalRel finalRanged finalWords =>
    have sem := supported_body_semantics program supported n final word sourceRun
    have ffi : FfiStateRel postFfi final.ffi := finalRel.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨final.ffi.ioEvents,sem,ffi.2.1⟩
private theorem bytesPairRel_eq (prod : List (UInt8 × UInt8)) (hol : List (BitVec 8 × BitVec 8))
    (rel : BytesPairRel prod hol) : hol = prod.map (fun pair => (byteToBits pair.1,byteToBits pair.2)) := by
  induction prod generalizing hol with
  | nil => cases hol <;> simp_all [BytesPairRel]
  | cons pair rest ih =>
    cases hol with
    | nil => simp [BytesPairRel] at rel
    | cons head tail =>
      simp only [BytesPairRel,List.map_cons,List.cons.injEq,Prod.mk.injEq] at rel
      have left : head.1 = byteToBits pair.1 := BitVec.eq_of_toNat_eq (by simpa [byteToBits_toNat] using rel.1.1)
      have right : head.2 = byteToBits pair.2 := BitVec.eq_of_toNat_eq (by simpa [byteToBits_toNat] using rel.1.2)
      have restEq := ih tail rel.2
      cases head
      simp_all

/-- An executable event list determines a unique exact HOL event list. -/
theorem ffiEventListRel_unique (prod : List FfiEvent) (a b : List HolIoEvent)
    (ha : FfiEventListRel prod a) (hb : FfiEventListRel prod b) : a = b := by
  induction prod generalizing a b with
  | nil => cases a <;> cases b <;> simp_all [FfiEventListRel]
  | cons head rest ih =>
    cases a with
    | nil => simp [FfiEventListRel] at ha
    | cons x xs =>
      cases b with
      | nil => simp [FfiEventListRel] at hb
      | cons y ys =>
        obtain ⟨hx,hxs⟩ := ha
        obtain ⟨hy,hys⟩ := hb
        have names : x.name = y.name := (sourceHolFfiName_of_rel head.name x.name hx.1).symm.trans
          (sourceHolFfiName_of_rel head.name y.name hy.1)
        have configs : x.configuration = y.configuration := (sourceBytesRel_eq _ _ hx.2.1).trans
          (sourceBytesRel_eq _ _ hy.2.1).symm
        have bytes : x.bytes = y.bytes := (bytesPairRel_eq _ _ hx.2.2).trans (bytesPairRel_eq _ _ hy.2.2).symm
        have same : x = y := by cases x; cases y; simp_all
        rw [same,ih xs ys hxs hys]
end SteppedFlapjack.Concrete
