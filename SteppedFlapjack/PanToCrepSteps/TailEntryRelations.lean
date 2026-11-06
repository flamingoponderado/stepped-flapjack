import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.PanToCrepSteps.WhileRiscV
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Call

/-! Ordinary frontend correctness supplies the zero-argument callee relations. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.PanSemStateFiniteExact

/-- Related caller states and a successful zero-argument source lookup determine
both the compiled callee and all frontend relations at the callee entry. -/
theorem tailEntry_call_relations {width : Nat} [NeZero width] {F : Type}
    (pan : PanSemStateFiniteExact width F) (crep : CrepSemHOLState width F)
    (context : PanToCrepContextExact width) (name : MlString) (body : ProgHOL width)
    (panLocals : HolFiniteMapExact MlString (ValueHOL width)) (returnShape : ShapeHOL)
    (lookup : lookupCodeHOLFinite pan.code.lookup name [] = some (body,panLocals,returnShape))
    (stateRel : panToCrepStateRelFiniteExact pan crep)
    (codeRel : codeRelExactHOLW context pan.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids pan.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context pan.locals crep.locals) :
    let calleeContext := ctxtFcExactHOL context.funcs context.eids [] [] []
    let crepEntry := decClockCrepSemHOL {crep with locals := HolFiniteMapExact.empty.updateList []}
    crep.code.lookup name = some ([],compileProgExactHOLW calleeContext body) ∧
    localisedProgHOL body = true ∧
    panToCrepStateRelFiniteExact (callEntryStateHOLFinite pan panLocals) crepEntry ∧
    codeRelExactHOLW calleeContext (callEntryStateHOLFinite pan panLocals).code crepEntry.code ∧
    panToCrepExcpRelFiniteExact calleeContext.eids (callEntryStateHOLFinite pan panLocals).eshapes ∧
    panToCrepLocalsRelFiniteExact calleeContext (callEntryStateHOLFinite pan panLocals).locals crepEntry.locals := by
  obtain ⟨params,src,_,hrel,_⟩ := lookupCodeHOLFinite_some_inv pan.code.lookup name [] body panLocals returnShape lookup
  have paramsNil : params = [] := by cases hrel; rfl
  subst params
  obtain ⟨params,sourceEntry,localised,_,_,_,targetLookup,calleeState,calleeCode,calleeExcp,calleeLocals⟩ :=
    pcCompileCorrectCallPrelude pan crep context name [] [] body panLocals returnShape
      (by rfl) lookup stateRel codeRel excpRel localsRel (by rfl)
  have same := Option.some.inj (sourceEntry.symm.trans src)
  have eq : params = [] := (Prod.mk.inj same).1
  subst params
  simp only [List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,List.range_zero,List.flatMap_nil,tlcHOL,
    List.zip, List.zipWith] at targetLookup calleeState calleeCode calleeExcp calleeLocals
  have target : crep.code.lookup name = some ([],compileProgExactHOLW
      (ctxtFcExactHOL context.funcs context.eids [] [] []) body) := by
    unfold lookupCodeFiniteHOL at targetLookup
    cases h : crep.code.lookup name with
    | none => simp [h] at targetLookup
    | some entry =>
      rcases entry with ⟨slots,prog⟩
      simp only [h] at targetLookup
      split at targetLookup
      · rename_i cond
        have nilSlots : slots = [] := by cases slots <;> simp_all
        subst slots
        simp only [Option.some.injEq,Prod.mk.injEq] at targetLookup
        simp only [targetLookup.1]
      · simp at targetLookup
  exact ⟨target,localised,calleeState,calleeCode,calleeExcp,calleeLocals⟩


/-- A successful source initializer and related initial states yield the actual
compiled initializer run and the corresponding zero-argument callee relations. -/
theorem tailEntry_init_call_relations {width : Nat} [NeZero width] {F : Type}
    (pan panMiddle : PanSemStateFiniteExact width F) (crep : CrepSemHOLState width F)
    (context : PanToCrepContextExact width) (init body : ProgHOL width) (name : MlString)
    (panLocals : HolFiniteMapExact MlString (ValueHOL width)) (returnShape : ShapeHOL)
    (initRun : pan.evaluateHOLFiniteState init = (none,panMiddle))
    (lookup : lookupCodeHOLFinite panMiddle.code.lookup name [] = some (body,panLocals,returnShape))
    (stateRel : panToCrepStateRelFiniteExact pan crep)
    (codeRel : codeRelExactHOLW context pan.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids pan.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context pan.locals crep.locals)
    (localised : localisedProgHOL init = true) :
    let calleeContext := ctxtFcExactHOL context.funcs context.eids [] [] []
    ∃ crepMiddle,
      evalCrepSemHOLProgExact crep (compileProgExactHOLW context init) = (none,crepMiddle) ∧
      crepMiddle.code.lookup name = some ([],compileProgExactHOLW calleeContext body) ∧
      localisedProgHOL body = true ∧
      panToCrepStateRelFiniteExact (callEntryStateHOLFinite panMiddle panLocals)
        (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}) ∧
      codeRelExactHOLW calleeContext (callEntryStateHOLFinite panMiddle panLocals).code
        (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).code ∧
      panToCrepExcpRelFiniteExact calleeContext.eids (callEntryStateHOLFinite panMiddle panLocals).eshapes ∧
      panToCrepLocalsRelFiniteExact calleeContext (callEntryStateHOLFinite panMiddle panLocals).locals
        (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).locals := by
  have correct : pcCompileCorrectAt init pan := (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨out,crepMiddle,run,postRel,postCode,postExcp,resultRel⟩ :=
    correct none panMiddle crep context initRun (by simp) stateRel codeRel excpRel localsRel localised
  obtain ⟨rfl,postLocals⟩ := resultRel
  have call := tailEntry_call_relations panMiddle crepMiddle context name body panLocals returnShape
    lookup postRel postCode postExcp postLocals
  exact ⟨crepMiddle,run,call⟩


/-- A completed source callee and successful initializer determine the actual
compiled Crep executions and their call-state relations. -/
theorem tailEntry_compiled_execution {F : Type}
    (pan panMiddle panPost : PanSemStateFiniteExact 64 F) (crep : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (init body : ProgHOL 64) (name : MlString)
    (panLocals : HolFiniteMapExact MlString (ValueHOL 64)) (returnShape : ShapeHOL)
    (panResult : Option (PanSemResultExact 64)) (complete : CompletePanResult panResult)
    (initRun : pan.evaluateHOLFiniteState init = (none,panMiddle))
    (lookup : lookupCodeHOLFinite panMiddle.code.lookup name [] = some (body,panLocals,returnShape))
    (clock : panMiddle.clock ≠ 0)
    (bodyRun : (callEntryStateHOLFinite panMiddle panLocals).evaluateHOLFiniteState body = (panResult,panPost))
    (stateRel : panToCrepStateRelFiniteExact pan crep)
    (codeRel : codeRelExactHOLW context pan.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids pan.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context pan.locals crep.locals)
    (localised : localisedProgHOL init = true) :
    let calleeContext := ctxtFcExactHOL context.funcs context.eids [] [] []
    ∃ crepMiddle crepPost crepResult,
      evalCrepSemHOLProgExact crep (compileProgExactHOLW context init) = (none,crepMiddle) ∧
      crepMiddle.code.lookup name = some ([],compileProgExactHOLW calleeContext body) ∧
      crepMiddle.clock ≠ 0 ∧ localisedProgHOL body = true ∧
      panToCrepStateRelFiniteExact (callEntryStateHOLFinite panMiddle panLocals)
        (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}) ∧
      codeRelExactHOLW calleeContext (callEntryStateHOLFinite panMiddle panLocals).code
        (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).code ∧
      panToCrepExcpRelFiniteExact calleeContext.eids (callEntryStateHOLFinite panMiddle panLocals).eshapes ∧
      panToCrepLocalsRelFiniteExact calleeContext (callEntryStateHOLFinite panMiddle panLocals).locals
        (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []}).locals ∧
      evalCrepSemHOLProgExact (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []})
        (compileProgExactHOLW calleeContext body) = (crepResult,crepPost) ∧
      CrepToLoopSteps.CompleteCrepResult crepResult ∧
      panToCrepStateRelFiniteExact panPost crepPost ∧
      pcCompileCorrectResultRel calleeContext panPost crepPost panResult crepResult := by
  have initCorrect : pcCompileCorrectAt init pan := (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨out,middle,run,postRel,postCode,postExcp,resultRel⟩ :=
    initCorrect none panMiddle crep context initRun (by simp) stateRel codeRel excpRel localsRel localised
  obtain ⟨rfl,postLocals⟩ := resultRel
  have crepClock : middle.clock ≠ 0 := by
    have eq : panMiddle.clock = middle.clock := postRel.2.2.2.2.2.1
    omega
  obtain ⟨found,bodyLocalised,calleeState,calleeCode,calleeExcp,calleeLocals⟩ :=
    tailEntry_call_relations panMiddle middle context name body panLocals returnShape
      lookup postRel postCode postExcp postLocals
  have nonerror : panResult ≠ some .error := by cases complete <;> simp
  have bodyCorrect : pcCompileCorrectAt body (callEntryStateHOLFinite panMiddle panLocals) :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨result,post,calleeRun,finalRel,_,_,finalResult⟩ :=
    bodyCorrect panResult panPost (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []})
      (ctxtFcExactHOL context.funcs context.eids [] [] []) bodyRun nonerror calleeState calleeCode calleeExcp
      calleeLocals bodyLocalised
  have crepComplete : CrepToLoopSteps.CompleteCrepResult result := by
    cases complete with
    | «return» value =>
      simp only [pcCompileCorrectResultRel] at finalResult
      rw [finalResult]
      exact .return _
    | ffi event =>
      simp only [pcCompileCorrectResultRel] at finalResult
      rw [finalResult]
      exact .ffi _
  exact ⟨middle,post,result,run,found,crepClock,bodyLocalised,calleeState,calleeCode,calleeExcp,calleeLocals,
    calleeRun,crepComplete,finalRel,finalResult⟩

end SteppedFlapjack.PanToCrepSteps
