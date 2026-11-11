import SteppedFlapjack.Concrete.NestedCalls
import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.Concrete.NestedCrep
import SteppedFlapjack.Concrete.Phase7SourceClock
import SteppedFlapjack.PanToCrepSteps.WhileSteps
import SteppedFlapjack.CrepToLoopSteps.CallFrontendShape

/-! Original HOL-shaped source execution for the nested-call witness. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

def nestedSourceState (bitmapWords : Nat) : PanSemStateFiniteExact 64 Unit :=
  let initial := sourceTemplateFor bitmapWords
  let mainCode := initial.code.update (ofString "main", ([], progToHOL nestedCallEntry, .one))
  let middleCode := mainCode.update (ofString "middle", ([], .call none (ofString "leaf") [], .one))
  let allCode := middleCode.update (ofString "leaf", ([], .return (.const 7), .one))
  {initial with code := allCode}

/-- Observational semantics starts from the original empty declaration state. -/
theorem nestedCall_declared_semantics (bitmapWords : Nat) :
    semanticsDecls {sourceTemplateFor bitmapWords with clock := 0} (ofString "main")
      (nestedCallDeclarations.map declToHOL) = semantics (nestedSourceState bitmapWords) (ofString "main") := by
  have same : semantics {nestedSourceState bitmapWords with clock := 0} (ofString "main") =
      semantics (nestedSourceState bitmapWords) (ofString "main") := by
    cases nestedSourceState bitmapWords
    rfl
  let fs : List (FunDeclHOL 64) :=
    [⟨ofString "main",false,true,[],progToHOL nestedCallEntry,.one⟩,
     ⟨ofString "middle",false,false,[],.call none (ofString "leaf") [],.one⟩,
     ⟨ofString "leaf",false,false,[],.return (.const 7),.one⟩]
  have wellFormed : fs.all (fun f =>
      f.params.all (fun p => isWfShapeExactHOL ([] : StructContextExact) p.2) &&
        isWfShapeExactHOL ([] : StructContextExact) f.returnShape) = true := by
    simp [fs,isWfShapeExactHOL]
  have sem := source_function_declarations_semantics
    {sourceTemplateFor bitmapWords with clock := 0} (ofString "main") fs wellFormed
  rw [← function_fold_code] at sem
  have sem' : semanticsDecls {sourceTemplateFor bitmapWords with clock := 0} (ofString "main")
      (nestedCallDeclarations.map declToHOL) =
      semantics {nestedSourceState bitmapWords with clock := 0} (ofString "main") := by
    simpa [fs,nestedCallDeclarations,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,nestedSourceState,
      sourceTemplateFor,sourceTemplate] using sem
  exact sem'.trans same

def nestedCountedProduction : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  {sourceProduction with code := functionEntries nestedCallDeclarations}

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
theorem nestedCounted_related : PanSemStateRelExec nestedCountedProduction (nestedSourceState 1).toExact := by
  have base := source_related (progToHOL nestedCallEntry)
  obtain ⟨hl,hg,hs,hc,he,hm,hmem,hshared,hclock,hbe,hffi,hbase,htop⟩ := base
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hl
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hg
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hs
  · intro name nameRanged
    have neq (other : String) (ranged : NameRanged other) (h : name ≠ other) : ofString name ≠ ofString other := by
      intro eq
      exact h (ofString_injective_of_ranged nameRanged ranged eq)
    have leafMain : ofString "leaf" ≠ ofString "main" := by decide
    have midMain : ofString "middle" ≠ ofString "main" := by decide
    have leafMid : ofString "leaf" ≠ ofString "middle" := by decide
    by_cases hmain : name = "main"
    · subst name
      simp [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,sourceProduction,sourceTemplate,
        PanSemStateFiniteExact.toExact,functionEntries,nestedCallDeclarations,panSemCodeLookup,lookupInfo,
        HolFiniteMapExact.lookup_update,FUPDATE,panLangEntryToHOL,shapeToHOL,progToHOL,expToHOL,nestedCallEntry,leafMain,midMain,leafMid]
    · by_cases hmiddle : name = "middle"
      · subst name
        simp [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,sourceProduction,sourceTemplate,
          PanSemStateFiniteExact.toExact,functionEntries,nestedCallDeclarations,panSemCodeLookup,lookupInfo,
          HolFiniteMapExact.lookup_update,FUPDATE,panLangEntryToHOL,shapeToHOL,progToHOL,expToHOL,nestedCallEntry,leafMain,midMain,leafMid]
      · by_cases hleaf : name = "leaf"
        · subst name
          simp [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,sourceProduction,sourceTemplate,
            PanSemStateFiniteExact.toExact,functionEntries,nestedCallDeclarations,panSemCodeLookup,lookupInfo,
            HolFiniteMapExact.lookup_update,FUPDATE,panLangEntryToHOL,shapeToHOL,progToHOL,expToHOL,nestedCallEntry,leafMain,midMain,leafMid]
        · have hm := neq "main" (by decide) hmain
          have hmid := neq "middle" (by decide) hmiddle
          have hl := neq "leaf" (by decide) hleaf
          simp [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,sourceProduction,sourceTemplate,
            PanSemStateFiniteExact.toExact,functionEntries,nestedCallDeclarations,panSemCodeLookup,lookupInfo,
            HolFiniteMapExact.lookup_update,FUPDATE,hm,hmid,hl,hmain,hmiddle,hleaf,
            Ne.symm hm,Ne.symm hmid,Ne.symm hl,Ne.symm hmain,Ne.symm hmiddle,Ne.symm hleaf]
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using he
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hm
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hmem
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hshared
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hclock
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hbe
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hffi
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using hbase
  · simpa [nestedCountedProduction,nestedSourceState,sourceTemplateFor_one,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplate] using htop

theorem nestedCounted_shapes :
    ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode nestedCountedProduction.code →
      ∃ scope, CallSupportedIn scope body := by
  intro name params body member
  simp [countedFunctionsOfCode,nestedCountedProduction,functionEntries,nestedCallDeclarations] at member
  rcases member with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · refine ⟨[],CallSupportedIn.call "answer" "middle" [] (by simp) ?_⟩
    exact .base (.ret (.local "answer" (by simp)))
  · exact ⟨[],.tail "leaf" [] (by simp)⟩
  · exact ⟨[],.base (.ret (.const _))⟩

theorem nestedCounted_run (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler nestedCountedProduction.structs
      (countedFunctionsOfCode nestedCountedProduction.code)
      nestedCountedProduction.baseAddress nestedCountedProduction.topAddress panSemBitVec64BytesInWord 8
      nestedCountedProduction.locals nestedCountedProduction.globals nestedCountedProduction.memory nestedCountedProduction.ffi
      nestedCallEntry (memoryAccess := some (panSemBitVec64MemoryAccess nestedCountedProduction))
      (contracts := some (countedContractsOfCode nestedCountedProduction.code [])) =
      some (.returned (fun _ => none) nestedCountedProduction.globals nestedCountedProduction.memory nestedCountedProduction.ffi [.word 7],6) := by
  simp [nestedCallEntry,nestedCountedProduction,sourceProduction,countedFunctionsOfCode,countedContractsOfCode,
    nestedCallDeclarations,functionEntries,evalPanValueFfiProgSteps,evalPanValueFfiCallSteps,panValueCallArguments,
    evalPanValueExpsCounted,evalPanValueExps,evalPanValueExp.evalPanValueExps,panValueExpsStepCost,
    panValueExpStepCost.panValueExpsStepCost,panValueCallTarget,lookupPanFunction,lookupInfo,panValueParametersValid,
    panValueValuesMatchShapes,bindPanValueParameters,panValueReturnValid,panValueReturnResult,
    evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,panShapeMatches,panValueShape,updatePanValueMap,
    restorePanValueFfiLocal]
  funext name
  simp [restorePanValueLocal]

theorem nestedCounted_source (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final, (nestedSourceState 1).evaluateHOLFiniteState (progToHOL nestedCallEntry) =
      (some (.returned (.val (.word 7))),final) ∧
      controlSteps (progToHOL nestedCallEntry) (nestedSourceState 1) ≤ 6 := by
  let _ : DecidablePred (nestedSourceState 1).memaddrs := by
    change DecidablePred ordinaryAddress
    infer_instance
  have shape : CallSupportedIn [] nestedCallEntry := by
    exact .call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp))))
  have ranged : PanSemStateRelExecRanged nestedCountedProduction := by
    simp [nestedCountedProduction,sourceProduction,PanSemStateRelExecRanged,StructContextByteRanged,StructContext.toHOL]
  have words : WordLocals nestedCountedProduction.locals := by
    simpa [nestedCountedProduction,sourceProduction] using wordLocals_empty
  have codeRanged : ∀ name entry, panSemCodeLookup nestedCountedProduction.code name = some entry → PanLangEntryByteRanged entry := by
    simpa [nestedCountedProduction,PanSemCodeRanged] using
      panSemCodeRanged_of_functionEntries sourceProduction nestedCallDeclarations nestedCall_declarations_ranged
  have budget : 6 ≤ (nestedSourceState 1).clock := by decide
  obtain ⟨result,final,hol,outcome,bound,_⟩ := supportedCalls_counted_source shape nestedCountedProduction
    (nestedSourceState 1) nestedCounted_related ranged words (by simp [nestedCallEntry,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged])
    codeRanged nestedCounted_shapes context primitive handler [] 8 6 _ (nestedCounted_run context primitive handler) budget
  cases outcome with
  | returned _ _ _ _ _ _ _ _ _ => exact ⟨final,hol,by simpa [countedErrorBonus] using bound⟩

/-- The original source entry returns the witness value with unchanged FFI. -/
theorem nestedCall_hol_run (bitmapWords : Nat) :
    ∃ final, evaluateHOLFiniteState {nestedSourceState bitmapWords with clock := 4}
      (.call none (ofString "main") []) =
      (some (.returned (.val (.word 7))),final) ∧ final.ffi = sourceFfi := by
  have leafMain : (ofString "leaf" == ofString "main") = false := by decide
  have middleMain : (ofString "middle" == ofString "main") = false := by decide
  have leafMiddle : (ofString "leaf" == ofString "middle") = false := by decide
  simp [leafMain,middleMain,leafMiddle,evaluateHOLFiniteState_call,nestedSourceState,sourceTemplateFor,nestedCallEntry,progToHOL,
    expToHOL,shapeToHOL,sourceTemplate,evalListHOLFinite,evalListHOLExact,
    PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,HolFiniteMapExact.lookup_update,FUPDATE,
    evaluateHOLFiniteState_decCall_fixClockRewrite,evaluateHOLFiniteState_return,callEntryStateHOLFinite,
    evalHOLExact,shapeOfHOLExact,shapeEqHOL,setVarHOLFinite,emptyLocalsHOLFinite]

/-- The original declarations terminate successfully without I/O events. -/
theorem nestedCall_source_semantics (bitmapWords : Nat) :
    semanticsDecls {sourceTemplateFor bitmapWords with clock := 0} (ofString "main")
      (nestedCallDeclarations.map declToHOL) = .terminate .success [] := by
  obtain ⟨final,run,ffi⟩ := nestedCall_hol_run bitmapWords
  rw [nestedCall_declared_semantics]
  have result := source_semantics_of_return (nestedSourceState bitmapWords) final (ofString "main") 4
    (.val (.word 7)) run
  simpa [ffi,sourceFfi] using result

/-- The HOL source run reaches five statement nodes across its two calls. -/
theorem nestedCall_controlSteps (bitmapWords : Nat) :
    controlSteps (.call none (ofString "main") []) {nestedSourceState bitmapWords with clock := 4} = 5 := by
  have leafMain : (ofString "leaf" == ofString "main") = false := by decide
  have middleMain : (ofString "middle" == ofString "main") = false := by decide
  have leafMiddle : (ofString "leaf" == ofString "middle") = false := by decide
  simp [controlSteps.eq_def,leafMain,middleMain,leafMiddle,evaluateHOLFiniteState_call,
    nestedSourceState,sourceTemplateFor,nestedCallEntry,progToHOL,expToHOL,shapeToHOL,sourceTemplate,
    evalListHOLFinite,evalListHOLExact,PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,
    HolFiniteMapExact.lookup_update,FUPDATE,
    evaluateHOLFiniteState_return,callEntryStateHOLFinite,evalHOLExact,shapeOfHOLExact,shapeEqHOL,
    setVarHOLFinite,emptyLocalsHOLFinite,fixClockHOLFinite]
  simp only [show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (3,a) (4,b) from
      by intro _ _; apply Prod.Lex.left; omega,
    show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (2,a) (3,b) from
      by intro _ _; apply Prod.Lex.left; omega,
    show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (1,a) (2,b) from
      by intro _ _; apply Prod.Lex.left; omega,
    show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (1,a) (3,b) from
      by intro _ _; apply Prod.Lex.left; omega, if_true]

/-- The entry with its ordinary call belongs to the call-aware frontend. -/
theorem nestedCall_frontend (ctxt : PanToCrepContextExact 64) : CallFrontend ctxt (progToHOL nestedCallEntry) := by
  simp only [nestedCallEntry,progToHOL,expToHOL,shapeToHOL]
  apply CallFrontend.decCall
  · simp
  · apply CallFrontend.base
    apply FrontendProgram.ret
    apply FrontendScalar.local (ofString "answer") (ctxt.vmax+1)
    simp [decCallSlots,HolFiniteMapExact.lookup_update,FUPDATE]

/-- The actual ordinary-call witness compiles into the optimizer's recursive
call-aware Loop shape in every compiler context. -/
theorem nestedCall_optimised_frontend_shape (ctxt : PanToCrepContextExact 64)
    (lc : CrepToLoopContextExact) (live : NumSet) :
    SteppedFlapjack.LoopLiveSteps.SimpleLoopSequenceSource
      (optimiseHOL (compileHOLExact lc live (compileProgExactHOLW ctxt (progToHOL nestedCallEntry)))) :=
  SteppedFlapjack.CrepToLoopSteps.callFrontend_optimised_loopShape (nestedCall_frontend ctxt) lc live

/-- The remaining functions provide the tail-call and return cases. -/
theorem nestedCall_callees_frontend (ctxt : PanToCrepContextExact 64) :
    CallFrontend ctxt (.call none (ofString "leaf") []) ∧
    CallFrontend ctxt (.return (.const 7)) := by
  exact ⟨.tail (by simp), .base (.ret (.const 7))⟩

/-- Every actual witness function has call-aware frontend syntax. -/
theorem nestedCall_frontendCode (bitmapWords : Nat) (ctxt : PanToCrepContextExact 64) : CallFrontendCode ctxt (nestedSourceState bitmapWords).code := by
  intro name params body rsh found
  simp only [nestedSourceState,sourceTemplateFor,sourceTemplate,HolFiniteMapExact.lookup_update,FUPDATE] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    exact (nestedCall_callees_frontend _).2
  · split at found
    · simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨rfl,rfl,rfl⟩ := found
      exact (nestedCall_callees_frontend _).1
    · split at found
      · simp only [Option.some.injEq,Prod.mk.injEq] at found
        obtain ⟨rfl,rfl,rfl⟩ := found
        exact nestedCall_frontend _
      · simp at found

theorem nestedCall_declaration_shapes :
    ∀ entry ∈ functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")),
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))) entry.2.2.1 := by
  intro entry member
  rw [nestedCall_lowered_declarations] at member
  simp only [functionsHOL,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h <;> subst entry
  · exact .seq (.base .skip) (.tail (by simp))
  · simpa only [nestedCallEntry,progToHOL,expToHOL,shapeToHOL,List.map_nil] using nestedCall_frontend _
  · exact .tail (by simp)
  · exact .base (.ret (.const 7))

theorem nestedCall_inline_selection_empty :
    (functionsHOL ((compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
  rw [nestedCall_lowered_declarations]
  rfl

theorem nestedCall_generated_table_supported :
    SteppedFlapjack.LoopLiveSteps.LoopTableSupported (sptFromAList (compileProgHOLExact Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa
      (compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))))) := by
  apply SteppedFlapjack.CrepToLoopSteps.callFrontend_declaration_loopTableSupported
  · exact nestedCall_inline_selection_empty
  · exact nestedCall_declaration_shapes

/-- The generated nested-call Crep execution consumes at most its actual
number of visits, with the code-table premise derived from source declarations. -/
theorem nestedCall_crep_clock_consumed :
    nestedCrepState.clock - (evalCrepSemHOLProgExact nestedCrepState
      (.seq .skip (.call none (ofString "main'") []))).2.clock ≤
      SteppedFlapjack.CrepSteps.steps (.seq .skip (.call none (ofString "main'") [])) nestedCrepState := by
  apply SteppedFlapjack.CrepSteps.callScalarProgram_clock_consumed
  · exact .seq (.base .skip) (.call none _ [] (by simp))
  · change SteppedFlapjack.CrepSteps.CallScalarTable (alistToFmapCodeExact
      (compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))))
    rw [compileProgDeclsHOLW,nestedCall_inline_selection_empty,CrepInlineRoute.compileInlTopHOLExact_nil]
    exact SteppedFlapjack.CrepToLoopSteps.callFrontend_crepTable _
      (SteppedFlapjack.CrepToLoopSteps.callFrontend_declaration_sources _ nestedCall_declaration_shapes)

end SteppedFlapjack.Concrete
