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

/-- The nested source and production state agree for any concrete bitmap length. -/
theorem nestedCounted_related_bitmaps (n : Nat) :
    PanSemStateRelExec {nestedCountedProduction with memory := fun a => some (.word (initialWordFor n a))}
      (nestedSourceState n).toExact := by
  change PanSemStateRelExec {nestedCountedProduction with memory := fun a => some (.word (initialWordFor n a))}
    {(nestedSourceState 1).toExact with memory := fun a => .word (initialWordFor n a)}
  obtain ⟨a,b,c,d,e,_,g,h,i,j,k,l,m⟩ := nestedCounted_related
  refine ⟨a,b,c,d,e,?_,g,h,i,j,k,l,m⟩
  intro addr member
  rfl

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

theorem nestedCounted_run (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler nestedCountedProduction.structs
      (countedFunctionsOfCode nestedCountedProduction.code)
      nestedCountedProduction.baseAddress nestedCountedProduction.topAddress panSemBitVec64BytesInWord 8
      nestedCountedProduction.locals nestedCountedProduction.globals memory nestedCountedProduction.ffi
      nestedCallEntry (memoryAccess := some (panSemBitVec64MemoryAccess {nestedCountedProduction with memory := memory}))
      (contracts := some (countedContractsOfCode nestedCountedProduction.code [])) =
      some (.returned (fun _ => none) nestedCountedProduction.globals memory nestedCountedProduction.ffi [.word 7],6) := by
  simp [nestedCallEntry,nestedCountedProduction,sourceProduction,countedFunctionsOfCode,countedContractsOfCode,
    nestedCallDeclarations,functionEntries,evalPanValueFfiProgSteps,evalPanValueFfiCallSteps,panValueCallArguments,
    evalPanValueExpsCounted,evalPanValueExps,evalPanValueExp.evalPanValueExps,panValueExpsStepCost,
    panValueExpStepCost.panValueExpsStepCost,panValueCallTarget,lookupPanFunction,lookupInfo,panValueParametersValid,
    panValueValuesMatchShapes,bindPanValueParameters,panValueReturnValid,panValueReturnResult,
    evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,panShapeMatches,panValueShape,updatePanValueMap,
    restorePanValueFfiLocal]
  funext name
  simp [restorePanValueLocal]

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

def nestedHOLFunctions : List (FunDeclHOL 64) :=
  [⟨ofString "main",false,true,[],progToHOL nestedCallEntry,.one⟩,
   ⟨ofString "middle",false,false,[],.call none (ofString "leaf") [],.one⟩,
   ⟨ofString "leaf",false,false,[],.return (.const 7),.one⟩]

theorem nestedHOLDeclarations : nestedHOLFunctions.map DeclHOL.function = nestedCallDeclarations.map declToHOL := by
  simp [nestedHOLFunctions,nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL]

theorem nestedHOLFunctionShapes : ∀ entry ∈ functionsHOL (nestedHOLFunctions.map DeclHOL.function),
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem nestedEntryShapes : ∀ entry ∈ functionsHOL (nestedCallDeclarations.map declToHOL),
    ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program := by
  rw [← nestedHOLDeclarations]
  intro entry member
  obtain ⟨names,program,_,body,supported,ranged⟩ := nestedHOLFunctionShapes entry member
  exact ⟨names,program,body,supported,ranged⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem nestedEntryCode : (nestedClockedSource).code = HolFiniteMapExact.empty.updateList
    (functionsHOL (nestedCallDeclarations.map declToHOL)).reverse := by
  apply HolFiniteMapExact.ext_lookup
  intro name
  simp [nestedClockedSource,nestedSourceState,sourceTemplateFor,sourceTemplate,HolFiniteMapExact.lookup_update,
    HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,nestedCallDeclarations,declToHOL,
    funDeclToHOL,functionsHOL,progToHOL,expToHOL,shapeToHOL]
  by_cases ha : name = ofString "main" <;> by_cases hb : name = ofString "middle" <;>
    by_cases hc : name = ofString "leaf" <;> simp_all [eq_comm]
  all_goals subst name; contradiction

end SteppedFlapjack.Concrete
