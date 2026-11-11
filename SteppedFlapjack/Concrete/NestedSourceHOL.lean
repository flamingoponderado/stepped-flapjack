import SteppedFlapjack.Concrete.CountedSpan
import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals
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
  have supported : CallSupportedIn [] nestedCallEntry :=
    .call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp))))
  exact callSupported_frontend_shape supported ctxt (by intro name member; simp at member)

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

private def nestedHOLFunctions : List (FunDeclHOL 64) :=
  [⟨ofString "main",false,true,[],progToHOL nestedCallEntry,.one⟩,
   ⟨ofString "middle",false,false,[],.call none (ofString "leaf") [],.one⟩,
   ⟨ofString "leaf",false,false,[],.return (.const 7),.one⟩]

private theorem nestedHOLDeclarations : nestedHOLFunctions.map DeclHOL.function = nestedCallDeclarations.map declToHOL := by
  simp [nestedHOLFunctions,nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL]

private theorem nestedHOLFunctionShapes : ∀ entry ∈ functionsHOL (nestedHOLFunctions.map DeclHOL.function),
    ∃ names, ∃ program : Prog (RiscV.Word 64),
      entry.2.1 = names.map (fun n => (ofString n,ShapeHOL.one)) ∧
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn names program ∧ ProgByteRanged program := by
  intro entry member
  simp [nestedHOLFunctions,functionsHOL] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨[],nestedCallEntry,rfl,rfl,?_,?_⟩
    · exact .call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp))))
    · simp [nestedCallEntry,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged]
  · refine ⟨[],.call none "leaf" [],rfl,by simp [progToHOL],?_,?_⟩
    · exact .tail "leaf" [] (by simp)
    · simp [ProgByteRanged,NameRanged]
  · refine ⟨[],.return (.const 7),rfl,by simp [progToHOL,expToHOL],?_,?_⟩
    · exact .base (.ret (.const _))
    · simp [ProgByteRanged,ExpByteRanged]

theorem nestedCall_noExceptions :
    getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")) =
      HolFiniteMapExact.empty := by
  have found : (functionsHOL (nestedHOLFunctions.map DeclHOL.function)).lookup (ofString "main") =
      some ([],progToHOL nestedCallEntry,.one) := by
    rw [nestedHOLDeclarations]
    simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,shapeToHOL]
  have result := functionOnly_noExceptions nestedHOLFunctions (ofString "main") (progToHOL nestedCallEntry) .one found
  simpa only [nestedHOLDeclarations] using result

theorem nestedCall_declaration_shapes : ∀ entry ∈ functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")),
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))) entry.2.2.1 := by
  rw [← nestedHOLDeclarations]
  apply functionOnly_callFrontend_shapes nestedHOLFunctions (ofString "main") (progToHOL nestedCallEntry) .one
  · rw [nestedHOLDeclarations]; simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,shapeToHOL]
  · exact nestedHOLFunctionShapes


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

/-- A replay clock equal to the counted source budget. -/
def nestedClockedSource : PanSemStateFiniteExact 64 Unit := {nestedSourceState 1 with clock := 6}
def nestedClockedProduction := {nestedCountedProduction with clock := 6}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedEntryShapes : ∀ entry ∈ functionsHOL (nestedCallDeclarations.map declToHOL),
    ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program := by
  rw [← nestedHOLDeclarations]
  intro entry member
  obtain ⟨names,program,_,body,supported,ranged⟩ := nestedHOLFunctionShapes entry member
  exact ⟨names,program,body,supported,ranged⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedEntryCode : (nestedClockedSource).code = HolFiniteMapExact.empty.updateList
    (functionsHOL (nestedCallDeclarations.map declToHOL)).reverse := by
  apply HolFiniteMapExact.ext_lookup
  intro name
  simp [nestedClockedSource,nestedSourceState,sourceTemplateFor,sourceTemplate,HolFiniteMapExact.lookup_update,
    HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,nestedCallDeclarations,declToHOL,
    funDeclToHOL,functionsHOL,progToHOL,expToHOL,shapeToHOL]
  by_cases ha : name = ofString "main" <;> by_cases hb : name = ofString "middle" <;>
    by_cases hc : name = ofString "leaf" <;> simp_all [eq_comm]
  all_goals subst name; contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedEntryCodeRel : PanSimp.CodeRel (nestedClockedSource).code (nestedClockedSource).code := by
  constructor
  · intro f h; exact h
  · intro f params body rsh found
    simp only [nestedClockedSource,nestedSourceState,sourceTemplateFor,sourceTemplate,HolFiniteMapExact.lookup_update,FUPDATE,
      HolFiniteMapExact.lookup_empty] at found ⊢
    repeat' split at found
    all_goals try simp only [Option.some.injEq,Prod.mk.injEq] at found
    all_goals rcases found with ⟨rfl,rfl,rfl⟩
    all_goals simp_all [beq_iff_eq,nestedCallEntry,progToHOL,expToHOL,shapeToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL]


open SteppedFlapjack.PanToCrepSteps

def nestedRenamedState : PanSemStateFiniteExact 64 Unit :=
  {nestedClockedSource with code := fpermCodeHOL (ofString "main") (newMainNameHOL (nestedCallDeclarations.map declToHOL)) (nestedClockedSource).code}

def nestedLoweredCode := HolFiniteMapExact.empty.updateList
  (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))).reverse

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The general counted source-to-Loop theorem applies to the nested-call example. -/
theorem nestedCounted_compilerLoop (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let lowered := compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")
    let programs := compileProgDeclsHOLW lowered
    let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
    let p : ProgHOL 64 := .seq .skip (.call none (ofString "main'") [])
    let crep := compileProgExactHOLW pan p
    let arch := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa
    let loop := concreteDeclLoopState arch nestedCrepState programs
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let limit := 4 * (1 + SimpVisits.simpTableFactor (functionsHOL (nestedCallDeclarations.map declToHOL)) * 6 +
      SimpVisits.hw (progToHOL (panSimpProg nestedCallEntry)) + 2)
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let budget := SteppedFlapjack.CrepToLoopSteps.callClockFactor ctxt rows nestedCrepState.clock crep * (limit+1)
    let factor := max (SteppedFlapjack.CrepToLoopSteps.callSyntaxCost ctxt crep) (SteppedFlapjack.LoopLiveSteps.loopCodeWeight loop.code+2)
    let loopLimit := SteppedFlapjack.CrepToLoopSteps.callSyntaxCost ctxt crep + factor * (nestedCrepState.clock+budget)
    let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
    let optFactor := max (SteppedFlapjack.CrepToLoopSteps.loopVisitWeight opt) (SteppedFlapjack.LoopLiveSteps.loopCodeWeight loop.code+2)
    ∃ lowerFinal post,
      (noGlobalsLoweredPreCall nestedRenamedState nestedLoweredCode).evaluateHOLFiniteState p =
        (some (.returned (.val (.word 7))),emptyLocalsHOLFinite lowerFinal) ∧
      Flapjack.LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt .ln crep) {loop with clock := loop.clock+budget} =
        (some (.result [.word 7]),post) ∧
      SteppedFlapjack.LoopSteps.steps (compileHOLExact ctxt .ln crep) {loop with clock := loop.clock+budget} ≤
        SteppedFlapjack.CrepToLoopSteps.callSyntaxCost ctxt crep + factor * (nestedCrepState.clock+budget) ∧
      Flapjack.LoopSemStateFiniteExact.evaluate opt {loop with clock := loop.clock+budget} =
        (some (.result [.word 7]),post) ∧
      SteppedFlapjack.LoopSteps.steps opt {loop with clock := loop.clock+budget} ≤
        SteppedFlapjack.CrepToLoopSteps.loopVisitWeight opt + optFactor * (2 * loopLimit) ∧
      post.ffi = lowerFinal.ffi := by
  let _ : DecidablePred (nestedClockedSource).memaddrs := by
    change DecidablePred ordinaryAddress
    infer_instance
  have shape : CallSupportedIn [] nestedCallEntry :=
    .call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp))))
  have ranged : PanSemStateRelExecRanged nestedClockedProduction := by
    simp [nestedClockedProduction,nestedCountedProduction,sourceProduction,PanSemStateRelExecRanged,StructContextByteRanged,StructContext.toHOL]
  have words : WordLocals nestedClockedProduction.locals := by
    simpa [nestedClockedProduction,nestedCountedProduction,sourceProduction] using wordLocals_empty
  have codeRanged : ∀ name entry, panSemCodeLookup nestedClockedProduction.code name = some entry → PanLangEntryByteRanged entry := by
    simpa [nestedClockedProduction,nestedCountedProduction,PanSemCodeRanged] using
      panSemCodeRanged_of_functionEntries sourceProduction nestedCallDeclarations nestedCall_declarations_ranged
  have outside : ¬ nestedClockedSource.memaddrs nestedClockedSource.topAddr := by
    simp [nestedClockedSource,nestedSourceState,sourceTemplateFor,sourceTemplate,ordinaryAddress,heapTop,fixtureHeapEnd,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  have aligned : panGlobalsByteAlignedHOL nestedClockedSource.topAddr := by
    change panGlobalsByteAlignedHOL heapTop
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  have result := countedCalls_functionOnlyLoop shape nestedClockedProduction nestedClockedSource
    (by
      obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := nestedCounted_related
      exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩) ranged words (by simp [nestedCallEntry,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged])
    codeRanged (by simpa [nestedClockedProduction] using nestedCounted_shapes) nestedClockedSource.code nestedEntryCodeRel
    (functionsHOL (nestedCallDeclarations.map declToHOL)) nestedEntryCode nestedEntryShapes
    nestedHOLFunctions (ofString "main")
    (by simpa only [nestedHOLDeclarations] using nestedEntryCode)
    (by rw [nestedHOLDeclarations]; simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,nestedCallEntry,panSimpProg,retToTail,seqAssoc,smartSeq,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,progToHOL,expToHOL,shapeToHOL])
    (by simp [nestedClockedSource,nestedSourceState,sourceTemplateFor,sourceTemplate,HolFiniteMapExact.lookup_update,FUPDATE,ofString,MlString.explode_implode])
    rfl rfl rfl rfl
    (by rw [nestedHOLDeclarations]; simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,shapeToHOL]; decide)
    nestedHOLFunctionShapes
    (by simpa only [nestedHOLDeclarations] using nestedCall_inline_selection_empty)
    outside aligned context primitive handler [] 8 6 _ _ _ _ 7
    (by simpa [nestedClockedProduction,panSemBitVec64MemoryAccess] using nestedCounted_run context primitive handler) (by decide) Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa
  obtain ⟨sourceFinal,lowerFinal,post,_,entry,loopRun,bound,optRun,optBound,ffi,_,_⟩ := result
  rw [nestedHOLDeclarations] at loopRun bound optRun optBound
  have codeWeight : CrepSteps.codeWeight (compileProgDeclsHOLW
      (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))) = 4 := by
    rw [nestedCall_crep_code]
    rfl
  simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,
    CrepSteps.statementWeight,codeWeight,show max 3 4 = 4 by decide] at loopRun bound optRun optBound
  refine ⟨lowerFinal,post,?_,?_,?_,?_,?_,ffi⟩
  · simpa [nestedHOLDeclarations,nestedRenamedState,nestedLoweredCode,newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode,nestedSeqHOL] using entry
  · simpa [nestedHOLDeclarations,nestedRenamedState,nestedLoweredCode,newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode,nestedSeqHOL,nestedCrepState,concreteDeclCrepState,noGlobalsLoweredPreCall,nestedClockedSource,nestedSourceState,sourceTemplateFor_one,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,Nat.add_assoc] using loopRun
  · simpa [nestedHOLDeclarations,nestedRenamedState,nestedLoweredCode,newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode,nestedSeqHOL,nestedCrepState,concreteDeclCrepState,noGlobalsLoweredPreCall,nestedClockedSource,nestedSourceState,sourceTemplateFor_one,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,Nat.add_assoc] using bound
  · simpa [nestedHOLDeclarations,nestedRenamedState,nestedLoweredCode,newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode,nestedSeqHOL,nestedCrepState,concreteDeclCrepState,noGlobalsLoweredPreCall,nestedClockedSource,nestedSourceState,sourceTemplateFor_one,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,Nat.add_assoc] using optRun
  · simpa [nestedHOLDeclarations,nestedRenamedState,nestedLoweredCode,newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode,nestedSeqHOL,nestedCrepState,concreteDeclCrepState,noGlobalsLoweredPreCall,nestedClockedSource,nestedSourceState,sourceTemplateFor_one,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,Nat.add_assoc] using optBound

end SteppedFlapjack.Concrete
