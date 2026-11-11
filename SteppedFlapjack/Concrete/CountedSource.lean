import SteppedFlapjack.Concrete.CountedScalar
import Flapjack.Pancake.Semantics.PanSem.TotalEvalRanged
import Flapjack.Pancake.Semantics.PanSem.TotalEvalCallBridge
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps Flapjack.Basis.Pure.MlString

/-- The counted evaluator table projected from the source code table. -/
def countedFunctionsOfCode (code : PanSemCodeMap (RiscV.Word 64)) :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  code.map (fun (name,params,body,_) => (name,params.map Prod.fst,body))

/-- Call contracts projected from the same source code table. -/
def countedContractsOfCode (code : PanSemCodeMap (RiscV.Word 64))
    (exceptions : InfoMap Shape) : PanValueCallContracts :=
  {parameterShapes := code.map (fun (name,params,_,_) => (name,params)),
   returnShapes := code.map (fun (name,_,_,ret) => (name,ret)), exceptionShapes := exceptions}

/-- Projecting the code table preserves function lookup. -/
theorem countedFunctionLookup (code : PanSemCodeMap (RiscV.Word 64)) (name : FunName) :
    lookupPanFunction name (countedFunctionsOfCode code) =
      (panSemCodeLookup code name).map (fun (params,body,_) => (params.map Prod.fst,body)) := by
  induction code with
  | nil => rfl
  | cons entry tail ih =>
    obtain ⟨n,params,body,ret⟩ := entry
    simp only [countedFunctionsOfCode,List.map_cons,lookupPanFunction,panSemCodeLookup,lookupInfo]
    by_cases h : name = n
    · subst n; simp
    · have h' : n ≠ name := Ne.symm h
      simp only [h,h',beq_iff_eq,if_false]
      simpa [countedFunctionsOfCode,panSemCodeLookup] using ih

/-- Both call evaluators perform the same argument-shape checks. -/
theorem codeArgumentShapes (structs : StructContext) (params : List (VarName × Shape))
    (values : List (PanValue (RiscV.Word 64))) :
    panSemCodeArgumentsMatch structs params values =
      panValueValuesMatchShapes structs (params.map Prod.snd) values := by
  induction params generalizing values with
  | nil => cases values <;> rfl
  | cons p ps ih => cases values with
    | nil => rfl
    | cons v vs => simp [panSemCodeArgumentsMatch,panValueValuesMatchShapes,ih]

/-- The generated call contract resolves the selected parameter shapes. -/
theorem countedParameterLookup (code : PanSemCodeMap (RiscV.Word 64))
    (exceptions : InfoMap Shape) (name : FunName) :
    lookupInfo name (countedContractsOfCode code exceptions).parameterShapes =
      (panSemCodeLookup code name).map (fun (params,_,_) => params) := by
  induction code with
  | nil => rfl
  | cons entry tail ih =>
    obtain ⟨n,params,body,ret⟩ := entry
    simp only [countedContractsOfCode,List.map_cons,lookupInfo,panSemCodeLookup]
    split <;> simp_all [countedContractsOfCode,panSemCodeLookup]

/-- The generated call contract resolves the selected return shape. -/
theorem countedReturnLookup (code : PanSemCodeMap (RiscV.Word 64))
    (exceptions : InfoMap Shape) (name : FunName) :
    lookupInfo name (countedContractsOfCode code exceptions).returnShapes =
      (panSemCodeLookup code name).map (fun (_,_,ret) => ret) := by
  induction code with
  | nil => rfl
  | cons entry tail ih =>
    obtain ⟨n,params,body,ret⟩ := entry
    simp only [countedContractsOfCode,List.map_cons,lookupInfo,panSemCodeLookup]
    split <;> simp_all [countedContractsOfCode,panSemCodeLookup]

/-- Counted and source call targets agree under generated contracts. -/
theorem countedCallTarget_eq (structs : StructContext) (code : PanSemCodeMap (RiscV.Word 64))
    (exceptions : InfoMap Shape) (name : FunName) (values : List (PanValue (RiscV.Word 64))) :
    panValueCallTarget structs (some (countedContractsOfCode code exceptions)) name
      (countedFunctionsOfCode code) values =
    (lookupPanSemCodeCall structs code name values).map (fun (body,_,locals) => (body,locals)) := by
  rw [panValueCallTarget,countedFunctionLookup]
  unfold lookupPanSemCodeCall
  cases hl : panSemCodeLookup code name with
  | none => simp
  | some entry =>
    obtain ⟨params,body,ret⟩ := entry
    simp only [Option.map_some]
    unfold panValueParametersValid
    simp only
    simp only [countedParameterLookup,hl,Option.map_some,codeArgumentShapes]
    split <;> simp_all
    split <;> simp_all

/-- The counted target is the source total evaluator target without its return shape. -/
theorem countedCallTarget_total {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (exceptions : InfoMap Shape)
    (name : FunName) (values : List (PanValue (RiscV.Word 64))) :
    panValueCallTarget state.structs (some (countedContractsOfCode state.code exceptions)) name
      (countedFunctionsOfCode state.code) values =
      (panSemTotalCodeLookup state name values).map (fun (body,locals,_) => (body,locals)) := by
  rw [countedCallTarget_eq]
  unfold panSemTotalCodeLookup
  cases h : lookupPanSemCodeCall state.structs state.code name values with
  | none => rfl
  | some entry => cases entry with | mk body rest => cases rest; rfl

open Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact in
/-- A declaration-driven counted call resolves the same callee and locals as
HOL, including missing and invalid calls. -/
theorem countedCallTarget_hol {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    (rel : PanSemStateRelExec state source.toExact) (exceptions : InfoMap Shape)
    (name : FunName) (nameRanged : NameRanged name) (values : List (PanValue (RiscV.Word 64)))
    (valuesRanged : ∀ value ∈ values, PanValueByteRanged value)
    (codeRanged : ∀ entry, panSemCodeLookup state.code name = some entry → PanLangEntryByteRanged entry) :
    match panValueCallTarget state.structs (some (countedContractsOfCode state.code exceptions)) name
        (countedFunctionsOfCode state.code) values,
      lookupCodeHOLFinite source.code.lookup (ofString name) (values.map panValueToHOL) with
    | none, none => True
    | some (callee, calleeLocals), some (body, exactLocals, exactShape) =>
        ∃ returnShape, lookupInfo name (countedContractsOfCode state.code exceptions).returnShapes = some returnShape ∧
        exactShape = shapeToHOL returnShape ∧ ShapeByteRanged returnShape ∧ body = progToHOL callee ∧ ProgByteRanged callee ∧
        (∀ name, NameRanged name → Option.map panValueToHOL (calleeLocals name) = exactLocals.lookup (ofString name)) ∧
        (∀ name value, calleeLocals name = some value → PanValueByteRanged value)
    | _, _ => False := by
  have agree := panSemTotalCodeLookup_agree state source rel (ofString name) values valuesRanged (by
    simpa only [toStringOfBytes_ofString_of_bytes name nameRanged] using codeRanged)
  rw [toStringOfBytes_ofString_of_bytes name nameRanged] at agree
  rw [countedCallTarget_total]
  cases prod : panSemTotalCodeLookup state name values with
  | none => cases h : lookupCodeHOLFinite source.code.lookup (ofString name) (values.map panValueToHOL) <;> simp_all
  | some entry =>
    obtain ⟨callee,locals,shape⟩ := entry
    cases h : lookupCodeHOLFinite source.code.lookup (ofString name) (values.map panValueToHOL) with
    | none => simp_all
    | some exactEntry =>
      obtain ⟨body,exactLocals,exactShape⟩ := exactEntry
      simp only [prod,h] at agree
      refine ⟨shape,?_,agree.2.1,agree.2.2.2.1,agree.1,agree.2.2.1,agree.2.2.2.2⟩
      simp only [countedReturnLookup,panSemTotalCodeLookup] at prod ⊢
      cases lookup : lookupPanSemCodeCall state.structs state.code name values with
      | none => simp [lookup] at prod
      | some entry =>
        obtain ⟨body',ret,locals'⟩ := entry
        simp only [lookup,Option.some.injEq,Prod.mk.injEq] at prod
        rw [← prod.2.2]
        unfold lookupPanSemCodeCall at lookup
        cases codeFound : panSemCodeLookup state.code name with
        | none => simp [codeFound] at lookup
        | some entry =>
          obtain ⟨params,body'',ret'⟩ := entry
          simp only [codeFound] at lookup
          change (if decide (params.map Prod.fst).Nodup && panSemCodeArgumentsMatch state.structs params values then
            (do let loc ← bindPanValueParameters (params.map Prod.fst) values; pure (body'',ret',loc))
            else none) = some (body',ret,locals') at lookup
          split at lookup
          · cases hbind : bindPanValueParameters (params.map Prod.fst) values <;> simp_all
          · simp at lookup


/-- Word-valued arguments produce word-valued callee locals. -/
theorem countedCallTarget_wordLocals (structs : StructContext) (contracts : Option PanValueCallContracts)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (name : FunName)
    (values : List (PanValue (RiscV.Word 64)))
    (valueWords : ∀ v ∈ values, ∃ word, v = .word word)
    (callee : Prog (RiscV.Word 64)) (locals : VarName → Option (PanValue (RiscV.Word 64)))
    (found : panValueCallTarget structs contracts name functions values = some (callee,locals)) :
    WordLocals locals := by
  unfold panValueCallTarget at found
  cases lookup : lookupPanFunction name functions with
  | none => simp [lookup] at found
  | some entry =>
    obtain ⟨params,body⟩ := entry
    simp only [lookup] at found
    split at found
    · cases bind : bindPanValueParameters params values with
      | none => simp [bind] at found
      | some bound =>
        simp only [bind,Option.some.injEq,Prod.mk.injEq] at found
        rw [← found.2]
        exact wordLocals_bind params values bound valueWords bind
    · simp at found

/-- Counted call-argument evaluation agrees with HOL, including failures. -/
theorem countedArguments_hol {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec state source.toExact)
    (ranged : PanSemStateRelExecRanged state) (expressions : List (Exp (RiscV.Word 64)))
    (exprRanged : ∀ e ∈ expressions, ExpByteRanged e) :
    (panValueCallArguments state.structs state.baseAddress state.topAddress panSemBitVec64BytesInWord
      state.locals state.globals state.memory expressions (some (panSemBitVec64MemoryAccess state))).map
      (fun pair => pair.1.map panValueToHOL) = source.evalListHOLFinite (expressions.map expToHOL) := by
  have agree := evalPanValueExps_eq_evalListHOLExact_of state.structs state.locals state.globals state.memory
    state.baseAddress state.topAddress panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state)) source
    expressions (fun e he => evalPanValueExp_agree state source rel ranged e (exprRanged e he))
  simpa [panValueCallArguments,evalPanValueExpsCounted,evalPanValueExps,Option.map_map,Function.comp_def] using agree

/-- Matching counted and HOL call targets produce related callee entry states. -/
theorem countedCallEntry_rel {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec state source.toExact) (ranged : PanSemStateRelExecRanged state)
    (exceptions : InfoMap Shape) (name : FunName) (nameRanged : NameRanged name)
    (scope : List VarName) (expressions : List (Exp (RiscV.Word 64)))
    (shape : ∀ e ∈ expressions, Scalar scope e) (exprRanged : ∀ e ∈ expressions, ExpByteRanged e)
    (words : WordLocals state.locals)
    (values : List (PanValue (RiscV.Word 64))) (cost : Nat)
    (arguments : panValueCallArguments state.structs state.baseAddress state.topAddress panSemBitVec64BytesInWord
      state.locals state.globals state.memory expressions (some (panSemBitVec64MemoryAccess state)) = some (values,cost))
    (codeRanged : ∀ entry, panSemCodeLookup state.code name = some entry → PanLangEntryByteRanged entry)
    (callee : Prog (RiscV.Word 64)) (calleeLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (found : panValueCallTarget state.structs (some (countedContractsOfCode state.code exceptions)) name
      (countedFunctionsOfCode state.code) values = some (callee,calleeLocals)) :
    ∃ holBody exactLocals returnShape,
      source.evalListHOLFinite (expressions.map expToHOL) = some (values.map panValueToHOL) ∧
      lookupCodeHOLFinite source.code.lookup (ofString name) (values.map panValueToHOL) =
        some (holBody,exactLocals,shapeToHOL returnShape) ∧
      lookupInfo name (countedContractsOfCode state.code exceptions).returnShapes = some returnShape ∧
      ShapeByteRanged returnShape ∧ holBody = progToHOL callee ∧ ProgByteRanged callee ∧
      PanSemStateRelExec {state with clock := state.clock-1, locals := calleeLocals}
        (callEntryStateHOLFinite source exactLocals).toExact ∧
      PanSemStateRelExecRanged {state with clock := state.clock-1, locals := calleeLocals} ∧
      WordLocals calleeLocals := by
  have valueWords := scalar_counted_arguments_words scope expressions shape state words values cost (by
    simpa [panValueCallArguments] using arguments)
  have valuesRanged : ∀ value ∈ values, PanValueByteRanged value := by
    intro value member
    obtain ⟨word,rfl⟩ := valueWords value member
    simp [PanValueByteRanged]
  have exactArgs : source.evalListHOLFinite (expressions.map expToHOL) = some (values.map panValueToHOL) := by
    have h := countedArguments_hol state source rel ranged expressions exprRanged
    rw [arguments] at h
    exact h.symm
  have correspondence := countedCallTarget_hol state source rel exceptions name nameRanged values valuesRanged codeRanged
  rw [found] at correspondence
  cases h : lookupCodeHOLFinite source.code.lookup (ofString name) (values.map panValueToHOL) with
  | none => simp [h] at correspondence
  | some entry =>
    obtain ⟨body,exactLocals,exactShape⟩ := entry
    simp only [h] at correspondence
    obtain ⟨returnShape,retLookup,retEq,retRanged,bodyEq,bodyRanged,localsRel,localsRanged⟩ := correspondence
    refine ⟨body,exactLocals,returnShape,exactArgs,?_,retLookup,retRanged,bodyEq,bodyRanged,?_,?_,?_⟩
    · rw [← retEq]
    · exact rel.callEntry calleeLocals exactLocals localsRel
    · exact ⟨localsRanged,ranged.2.1,ranged.2.2⟩
    · exact countedCallTarget_wordLocals _ _ _ _ _ valueWords callee calleeLocals found

/-- Result relation for the call-free scalar source fragment. -/
inductive CountedOutcome {σ : Type} (initial : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanValueFfiControlResult (RiscV.Word 64) σ → Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 σ → Prop
  | normal (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock} final.toExact)
      (ranged : PanSemStateRelExecRanged {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock})
      (words : WordLocals locals) : CountedOutcome initial (.normal locals globals memory ffi) none final
  | returned (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (word : BitVec 64) (final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock} final.toExact)
      (ranged : PanSemStateRelExecRanged {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock})
      (words : WordLocals locals) : CountedOutcome initial (.returned locals globals memory ffi [.word word])
        (some (.returned (.val (.word word)))) final

  | error (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock} final.toExact)
      (ranged : PanSemStateRelExecRanged {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock})
      (words : WordLocals locals) : CountedOutcome initial (.error locals globals memory ffi) (some .error) final

/-- Runtime fields may be threaded between statements without changing the
persistent source machine context carried by the result relation. -/
private theorem outcomeRebase {σ : Type}
    (initial : PanSemState (RiscV.Word 64) (FfiState σ))
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (clock : Nat)
    {result : PanValueFfiControlResult (RiscV.Word 64) σ} {hol : Option (PanSemResultExact 64)}
    {final : PanSemStateFiniteExact 64 σ}
    (outcome : CountedOutcome {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := clock}
      result hol final) : CountedOutcome initial result hol final := by
  cases outcome with
  | normal l g m f final rel ranged words =>
    exact .normal l g m f final (by simpa using rel) (by simpa using ranged) words
  | returned l g m f word final rel ranged words =>
    exact .returned l g m f word final (by simpa using rel) (by simpa using ranged) words
  | error l g m f final rel ranged words =>
    exact .error l g m f final (by simpa using rel) (by simpa using ranged) words

def CountedNonError {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Prop
  | .error _ _ _ _ => False
  | _ => True

/-- A failed expression costs zero counted steps but still visits its statement. -/
def countedErrorBonus {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Nat
  | .error _ _ _ _ => 1
  | _ => 0

private def Bridge (invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop)
    (contracts : Option PanValueCallContracts) (limit : Nat) (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs],
    PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production → WordLocals production.locals →
    ProgByteRanged program → ∀ (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
      (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
      (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
      (result : PanValueFfiControlResult (RiscV.Word 64) σ),
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) = some (result,count) →
      count ≤ source.clock → fuel ≤ limit → invariant production.code functions →
      ∃ holResult sourceFinal,
        source.evaluateHOLFiniteState (progToHOL program) = (holResult,sourceFinal) ∧
        CountedOutcome production result holResult sourceFinal ∧
        controlSteps (progToHOL program) source ≤ count + countedErrorBonus result ∧ source.clock ≤ sourceFinal.clock + count

private theorem errorLeaf {σ : Type} (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (program : Prog (RiscV.Word 64)) (count : Nat)
    (hol : source.evaluateHOLFiniteState (progToHOL program) = (some .error,source))
    (visits : controlSteps (progToHOL program) source = 1) :
    ∃ holResult sourceFinal,
      source.evaluateHOLFiniteState (progToHOL program) = (holResult,sourceFinal) ∧
      CountedOutcome production (.error production.locals production.globals production.memory production.ffi) holResult sourceFinal ∧
      controlSteps (progToHOL program) source ≤ count + countedErrorBonus (.error production.locals production.globals production.memory production.ffi) ∧
      source.clock ≤ sourceFinal.clock + count := by
  have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
  refine ⟨some .error,source,hol,?_,?_,by omega⟩
  · apply CountedOutcome.error
    · simpa [clockEq] using rel
    · simpa [clockEq] using ranged
    · exact words
  · simp [visits,countedErrorBonus]

private theorem skipBridge {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} {limit : Nat} : Bridge invariant contracts limit .skip := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,Option.some.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
    refine ⟨none,source,?_,?_,?_,?_⟩
    · simp only [progToHOL,evaluateHOLFiniteState_skip]
    · apply CountedOutcome.normal
      · simpa [clockEq] using rel
      · simpa [clockEq] using ranged
      · exact words
    · simp [progToHOL,controlSteps.eq_def]
    · omega
private theorem returnBridge {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} {limit : Nat} : Bridge invariant contracts limit (.return expression) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    have originalRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
        production.locals production.globals production.memory production.ffi (.return expression)
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count) := by
      simpa only [evalPanValueFfiProgSteps] using run
    simp only [evalPanValueFfiProgSteps,panValueReturnResult,evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none =>
      simp only [evaluated,Option.map_none,Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      have exprRanged : ExpByteRanged expression := by simpa [ProgByteRanged] using byteRanged
      obtain ⟨_,hol,visits⟩ := counted_scalar_return_error production source rel ranged words expression scalar exprRanged
        context primitive handler functions (fuel+1) 0 originalRun
      exact errorLeaf production source rel ranged words (.return expression) 0 (by simpa [progToHOL] using hol)
        (by simpa [progToHOL] using visits)
    | some value =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some value := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
        have exprRanged : ExpByteRanged expression := by simpa [ProgByteRanged] using byteRanged
        have inverted := counted_return_invert production source rel ranged expression exprRanged word
          context primitive handler functions (fuel+1) (panValueExpStepCost expression+1) originalRun
        obtain ⟨hol,finalRel,finalRanged,bound⟩ := inverted
        have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
        refine ⟨some (.returned (.val (.word word))),source.emptyLocalsHOLFinite,?_,?_,?_,?_⟩
        · simpa [progToHOL] using hol
        · apply CountedOutcome.returned
          · simpa [emptyLocalsHOLFinite,panEmptyLocals,clockEq] using finalRel
          · simpa [emptyLocalsHOLFinite,panEmptyLocals,clockEq] using finalRanged
          · exact wordLocals_empty
        · simpa [progToHOL,countedErrorBonus] using bound
        · simp [emptyLocalsHOLFinite]
      · have expressionRun : evalPanSemStateExp production expression = some value := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
        rename_i invalid
        simp at invalid

private theorem assignBridge {scope : List VarName} (name : VarName) {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} {limit : Nat} : Bridge invariant contracts limit (.assign .local name expression) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  have nameRanged : NameRanged name := by simpa [ProgByteRanged] using byteRanged.1
  have exprRanged : ExpByteRanged expression := by simpa [ProgByteRanged] using byteRanged.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    have originalRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
        production.locals production.globals production.memory production.ffi (.assign .local name expression)
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count) := by
      simpa only [evalPanValueFfiProgSteps] using run
    simp only [evalPanValueFfiProgSteps,panValueAssignLocalResult,evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none =>
      simp only [evaluated,Option.map_none,Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      obtain ⟨hol,visits⟩ := counted_assign_error production source rel ranged name nameRanged expression exprRanged
        context primitive handler functions (fuel+1) 0 originalRun
      exact errorLeaf production source rel ranged words (.assign .local name expression) 0 (by simpa [progToHOL] using hol)
        (by simpa [progToHOL] using visits)
    | some value =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some value := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
        obtain ⟨assigned,postEq,hol,finalRel,finalRanged,bound⟩ :=
          counted_assign_invert production source rel ranged name nameRanged expression exprRanged
            context primitive handler functions (fuel+1) (panValueExpStepCost expression+1)
            (updatePanValueMap production.locals name (.word word)) originalRun
        have valueEq : assigned = .word word := by
          have h := congrFun postEq name
          simpa [updatePanValueMap] using h.symm
        subst assigned
        let final := setVarHOLFinite (ofString name) (.val (.word word)) source
        have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
        refine ⟨none,final,?_,?_,?_,?_⟩
        · simpa [progToHOL,panValueToHOL,final] using hol
        · apply CountedOutcome.normal
          · simpa [final,setVarHOLFinite,clockEq] using finalRel
          · simpa [final,setVarHOLFinite,clockEq] using finalRanged
          · exact wordLocals_update words name word
        · simpa [progToHOL,final,countedErrorBonus] using bound
        · simp [final,setVarHOLFinite]
      · simp only [Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨hol,visits⟩ := counted_assign_error production source rel ranged name nameRanged expression exprRanged
          context primitive handler functions (fuel+1) (panValueExpStepCost expression+1) originalRun
        exact errorLeaf production source rel ranged words (.assign .local name expression) (panValueExpStepCost expression+1)
          (by simpa [progToHOL] using hol) (by simpa [progToHOL] using visits)

private theorem iteBridge {scope : List VarName} {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} {limit : Nat} (aBound : Bridge invariant contracts limit a) (bBound : Bridge invariant contracts limit b) : Bridge invariant contracts (limit+1) (.ite condition a b) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  have condRanged : ExpByteRanged condition := by simpa [ProgByteRanged] using byteRanged.1
  have aRanged : ProgByteRanged a := by simpa [ProgByteRanged] using byteRanged.2.1
  have bRanged : ProgByteRanged b := by simpa [ProgByteRanged] using byteRanged.2.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps] at run
    cases condRun : panValueIteCondition production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
        production.locals production.globals production.memory condition (some (panSemBitVec64MemoryAccess production)) with
    | none =>
      simp [condRun] at run
      obtain ⟨rfl,rfl⟩ := run
      have condExact := counted_scalar_condition_error production source rel ranged words condition scalar condRanged condRun
      apply errorLeaf production source rel ranged words (.ite condition a b) 0
      · simp only [progToHOL]
        rw [evaluateHOLFiniteState_ite,condExact]
      · simp only [progToHOL]
        rw [controlSteps_ite,condExact]
        rfl
    | some pair =>
      rcases pair with ⟨word,condCost⟩
      have condExact := (counted_condition_invert production source rel ranged condition condRanged word condCost condRun).1
      by_cases zero : word = 0
      · cases branchRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
            production.locals production.globals production.memory production.ffi b
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
        | none => simp [condRun,zero,branchRun] at run
        | some branch =>
          rcases branch with ⟨branchResult,branchCost⟩
          simp [condRun,zero,branchRun] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨holResult,sourceFinal,hol,outcome,bound,clock⟩ := bBound production source rel ranged words bRanged
            context primitive handler functions fuel branchCost branchResult branchRun (by omega) (by omega) codeOk
          refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
          · simp only [progToHOL]
            rw [evaluateHOLFiniteState_ite,condExact]
            simpa [zero] using hol
          · simp only [progToHOL]
            rw [controlSteps_ite,condExact]
            simp only [zero,ne_eq,not_true_eq_false,if_false]
            omega
      · have zeroBits : word ≠ (0#64) := by simpa using zero
        cases branchRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
            production.locals production.globals production.memory production.ffi a
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
        | none => simp [condRun,zeroBits,branchRun] at run
        | some branch =>
          rcases branch with ⟨branchResult,branchCost⟩
          simp [condRun,zeroBits,branchRun] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨holResult,sourceFinal,hol,outcome,bound,clock⟩ := aBound production source rel ranged words aRanged
            context primitive handler functions fuel branchCost branchResult branchRun (by omega) (by omega) codeOk
          refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
          · simp only [progToHOL]
            rw [evaluateHOLFiniteState_ite,condExact]
            simpa [zeroBits] using hol
          · simp only [progToHOL]
            rw [controlSteps_ite,condExact]
            simp only [if_pos zero]
            omega

private theorem seqBridge {a b : Prog (RiscV.Word 64)}
    {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} {limit : Nat} (aBound : Bridge invariant contracts limit a) (bBound : Bridge invariant contracts limit b) : Bridge invariant contracts (limit+1) (.seq a b) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  have aRanged : ProgByteRanged a := by simpa [ProgByteRanged] using byteRanged.1
  have bRanged : ProgByteRanged b := by simpa [ProgByteRanged] using byteRanged.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps] at run
    cases firstRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi a
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
    | none => simp [firstRun] at run
    | some first =>
      rcases first with ⟨firstResult,firstCost⟩
      cases firstResult with
      | normal nextLocals nextGlobals nextMemory nextFfi =>
        cases secondRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
            nextLocals nextGlobals nextMemory nextFfi b
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
        | none => simp [firstRun,secondRun] at run
        | some second =>
          rcases second with ⟨secondResult,secondCost⟩
          simp [firstRun,secondRun] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨firstHol,sourceMiddle,holFirst,firstOutcome,firstBound,firstClock⟩ :=
            aBound production source rel ranged words aRanged context primitive handler functions fuel firstCost
              (.normal nextLocals nextGlobals nextMemory nextFfi) firstRun (by omega) (by omega) codeOk
          simp only [countedErrorBonus,Nat.add_zero] at firstBound
          cases firstOutcome with
          | normal l g m f final nextRel nextRanged nextWords =>
            have memEq : sourceMiddle.memaddrs = source.memaddrs := by
              funext address
              apply propext
              exact (nextRel.2.2.2.2.2.2.1 address).symm.trans (rel.2.2.2.2.2.2.1 address)
            let _ : DecidablePred sourceMiddle.memaddrs := by rw [memEq]; exact dec
            let next := {production with locals := nextLocals, globals := nextGlobals, memory := nextMemory, ffi := nextFfi, clock := sourceMiddle.clock}
            have nextRun : evalPanValueFfiProgSteps context primitive handler next.structs functions
                next.baseAddress next.topAddress panSemBitVec64BytesInWord fuel
                next.locals next.globals next.memory next.ffi b (memoryAccess := some (panSemBitVec64MemoryAccess next)) (contracts := contracts) =
                some (secondResult,secondCost) := by simpa [next,panSemBitVec64MemoryAccess] using secondRun
            obtain ⟨holResult,sourceFinal,holSecond,secondOutcome,secondBound,secondClock⟩ :=
              bBound next sourceMiddle nextRel nextRanged nextWords bRanged context primitive handler functions fuel secondCost
                secondResult nextRun (by omega) (by omega) codeOk
            refine ⟨holResult,sourceFinal,?_,?_,?_,by omega⟩
            · simp only [progToHOL]
              rw [evaluateHOLFiniteState_seq_line780,holFirst]
              exact holSecond
            · exact outcomeRebase production nextLocals nextGlobals nextMemory nextFfi sourceMiddle.clock secondOutcome
            · simp only [progToHOL]
              rw [controlSteps_seq,holFirst]
              simp only
              omega
      | returned l g m f values =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨holResult,sourceFinal,holFirst,outcome,firstBound,firstClock⟩ :=
          aBound production source rel ranged words aRanged context primitive handler functions fuel firstCost
            (.returned l g m f values) firstRun (by omega) (by omega) codeOk
        refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
        · simp only [progToHOL]
          rw [evaluateHOLFiniteState_seq_line780,holFirst]
          cases outcome; simp
        · simp only [progToHOL]
          rw [controlSteps_seq,holFirst]
          cases outcome; simp only; omega
      | error l g m f =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨holResult,sourceFinal,holFirst,outcome,firstBound,firstClock⟩ :=
          aBound production source rel ranged words aRanged context primitive handler functions fuel firstCost
            (.error l g m f) firstRun (by omega) (by omega) codeOk
        simp only [countedErrorBonus] at firstBound
        refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
        · simp only [progToHOL]
          rw [evaluateHOLFiniteState_seq_line780,holFirst]
          cases outcome; simp
        · simp only [progToHOL]
          rw [controlSteps_seq,holFirst]
          cases outcome; simp only [countedErrorBonus]; omega
      | raised l g m f e v =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨_,_,_,outcome,_,_⟩ := aBound production source rel ranged words aRanged
          context primitive handler functions fuel firstCost (.raised l g m f e v) firstRun (by omega) (by omega) codeOk
        cases outcome
      | broke l g m f =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨_,_,_,outcome,_,_⟩ := aBound production source rel ranged words aRanged
          context primitive handler functions fuel firstCost (.broke l g m f) firstRun (by omega) (by omega) codeOk
        cases outcome
      | continued l g m f =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨_,_,_,outcome,_,_⟩ := aBound production source rel ranged words aRanged
          context primitive handler functions fuel firstCost (.continued l g m f) firstRun (by omega) (by omega) codeOk
        cases outcome
      | finalFfi l g m f e =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨_,_,_,outcome,_,_⟩ := aBound production source rel ranged words aRanged
          context primitive handler functions fuel firstCost (.finalFfi l g m f e) firstRun (by omega) (by omega) codeOk
        cases outcome

private theorem restoreOutcome {σ : Type}
    (initial : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ)
    (rel : PanSemStateRelExec initial source.toExact) (ranged : PanSemStateRelExecRanged initial)
    (words : WordLocals initial.locals) (name : VarName) (nameRanged : NameRanged name)
    (word : BitVec 64) {result : PanValueFfiControlResult (RiscV.Word 64) σ}
    {hol : Option (PanSemResultExact 64)} {final : PanSemStateFiniteExact 64 σ}
    (outcome : CountedOutcome {initial with locals := updatePanValueMap initial.locals name (.word word)} result hol final) :
    CountedOutcome initial (restorePanValueFfiLocal name (initial.locals name) result) hol
      {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))} := by
  have saved := rel.1 name nameRanged
  have restoreEq (current : VarName → Option (PanValue (RiscV.Word 64))) :
      restorePanValueLocal current name (initial.locals name) = resVar current (name,initial.locals name) := by
    funext key
    by_cases same : key = name
    · subst key; cases initial.locals name <;> simp [restorePanValueLocal,resVar,FDOMSUB,FUPDATE]
    · have reverse : name ≠ key := Ne.symm same
      cases initial.locals name <;> simp [restorePanValueLocal,resVar,FDOMSUB,FUPDATE,same,reverse]
  cases outcome with
  | normal l g m f final nextRel nextRanged nextWords =>
    simp only [restorePanValueFfiLocal]
    apply CountedOutcome.normal
    · have h := nextRel.resVarLocals name nameRanged (initial.locals name)
      simpa [restoreEq, saved] using h
    · have h := PanSemStateRelExecRanged.resVarLocals nextRanged name (initial.locals name) (ranged.1 name)
      simpa [restoreEq] using h
    · exact wordLocals_restore nextWords words name
  | returned l g m f value final nextRel nextRanged nextWords =>
    simp only [restorePanValueFfiLocal]
    apply CountedOutcome.returned
    · have h := nextRel.resVarLocals name nameRanged (initial.locals name)
      simpa [restoreEq, saved] using h
    · have h := PanSemStateRelExecRanged.resVarLocals nextRanged name (initial.locals name) (ranged.1 name)
      simpa [restoreEq] using h
    · exact wordLocals_restore nextWords words name
  | error l g m f final nextRel nextRanged nextWords =>
    simp only [restorePanValueFfiLocal]
    apply CountedOutcome.error
    · have h := nextRel.resVarLocals name nameRanged (initial.locals name)
      simpa [restoreEq, saved] using h
    · have h := PanSemStateRelExecRanged.resVarLocals nextRanged name (initial.locals name) (ranged.1 name)
      simpa [restoreEq] using h
    · exact wordLocals_restore nextWords words name

private theorem declBridge {scope : List VarName} (name : VarName) {initializer : Exp (RiscV.Word 64)}
    {body : Prog (RiscV.Word 64)} (scalar : Scalar scope initializer) {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} {limit : Nat} (bodyBound : Bridge invariant contracts limit body) :
    Bridge invariant contracts (limit+1) (.dec name .one initializer body) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  have nameRanged : NameRanged name := by simpa [ProgByteRanged] using byteRanged.1
  have initRanged : ExpByteRanged initializer := by simpa [ProgByteRanged] using byteRanged.2.2.1
  have bodyRanged : ProgByteRanged body := by simpa [ProgByteRanged] using byteRanged.2.2.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps] at run
    cases initRun : panValueDecAccepted production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
        production.locals production.globals production.memory initializer (some (panSemBitVec64MemoryAccess production)) .one with
    | none =>
      simp [initRun] at run
      obtain ⟨rfl,rfl⟩ := run
      have initExact := counted_scalar_initializer_error production source rel ranged words initializer scalar initRanged initRun
      apply errorLeaf production source rel ranged words (.dec name .one initializer body) 0
      · simp only [progToHOL,shapeToHOL]
        rw [evaluateHOLFiniteState_dec_total]
        simp only [initExact]
      · simp only [progToHOL,shapeToHOL]
        rw [controlSteps.eq_def]
        simp [initExact]
    | some pair =>
      rcases pair with ⟨value,initCost⟩
      obtain ⟨word,rfl,costEq,initHol⟩ := counted_scalar_initializer_invert production source rel ranged words initializer
        scalar initRanged value initCost initRun
      subst initCost
      let entry := {production with locals := updatePanValueMap production.locals name (.word word)}
      let sourceEntry := setVarHOLFinite (ofString name) (.val (.word word)) source
      have entryRel : PanSemStateRelExec entry sourceEntry.toExact := by
        simpa [entry,sourceEntry,panValueToHOL] using rel.updateLocals name nameRanged (.word word)
      have entryRanged : PanSemStateRelExecRanged entry := by
        exact PanSemStateRelExecRanged.updateLocals ranged name (.word word) (by simp [PanValueByteRanged])
      have entryWords : WordLocals entry.locals := wordLocals_update words name word
      let _ : DecidablePred sourceEntry.memaddrs := dec
      cases bodyRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
          (updatePanValueMap production.locals name (.word word)) production.globals production.memory production.ffi body
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
      | none => simp [initRun,bodyRun] at run
      | some pair =>
        rcases pair with ⟨bodyResult,bodyCost⟩
        simp [initRun,bodyRun] at run
        obtain ⟨rfl,rfl⟩ := run
        have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
            entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
            (memoryAccess := some (panSemBitVec64MemoryAccess entry)) (contracts := contracts) = some (bodyResult,bodyCost) := by
          simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
        obtain ⟨holResult,bodyFinal,hol,outcome,bound,clock⟩ := bodyBound entry sourceEntry entryRel entryRanged entryWords bodyRanged
          context primitive handler functions fuel bodyCost bodyResult entryRun (by simp [sourceEntry,setVarHOLFinite]; omega) (by omega) codeOk
        have valid : shapeEqHOL .one (shapeOfHOLExact (.val (.word word))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
        have bonusEq : countedErrorBonus (restorePanValueFfiLocal name (production.locals name) bodyResult) = countedErrorBonus bodyResult := by
          cases bodyResult <;> rfl
        refine ⟨holResult,{bodyFinal with locals := HolFiniteMapExact.resVarEq bodyFinal.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_,?_⟩
        · simp only [progToHOL,shapeToHOL]
          rw [evaluateHOLFiniteState_dec_total]
          simp only [initHol,valid,if_true]
          rw [show (setVarHOLFinite (ofString name) (.val (.word word)) source).evaluateHOLFiniteState (progToHOL body) = (holResult,bodyFinal) from hol]
        · exact restoreOutcome production source rel ranged words name nameRanged word outcome
        · simp only [progToHOL,shapeToHOL]
          rw [controlSteps_dec _ _ _ _ _ _ initHol valid,bonusEq]
          simp only [sourceEntry] at bound
          omega
        · simp [sourceEntry,setVarHOLFinite] at clock
          simp only
          omega

private theorem whileBridge {scope : List VarName} {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} {limit : Nat} (bodyBound : Bridge invariant contracts limit body) : Bridge invariant contracts (limit+1) (.while condition body) := by
  have loopAt : ∀ fuel {σ : Type} (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs],
      PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production → WordLocals production.locals →
      ProgByteRanged (.while condition body) → ∀ (context : PanValueFfiContext (RiscV.Word 64))
      (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
      (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (count : Nat)
      (result : PanValueFfiControlResult (RiscV.Word 64) σ),
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi (.while condition body)
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) = some (result,count) →
      count ≤ source.clock → fuel ≤ limit+1 → invariant production.code functions →
      ∃ holResult sourceFinal, source.evaluateHOLFiniteState (progToHOL (.while condition body)) = (holResult,sourceFinal) ∧
        CountedOutcome production result holResult sourceFinal ∧
        controlSteps (progToHOL (.while condition body)) source ≤ count + countedErrorBonus result ∧ source.clock ≤ sourceFinal.clock + count := by
    intro fuel
    induction fuel with
    | zero =>
      intro σ production source dec rel ranged words byteRanged context primitive handler functions count result run
      simp [evalPanValueFfiProgSteps] at run
    | succ fuel ih =>
      intro σ production source dec rel ranged words byteRanged context primitive handler functions count result run budget fuelBound codeOk
      have condRanged : ExpByteRanged condition := by simpa [ProgByteRanged] using byteRanged.1
      have bodyRanged : ProgByteRanged body := by simpa [ProgByteRanged] using byteRanged.2
      simp only [evalPanValueFfiProgSteps] at run
      cases condRun : panValueIteCondition production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
          production.locals production.globals production.memory condition (some (panSemBitVec64MemoryAccess production)) with
      | none =>
        simp [condRun] at run
        obtain ⟨rfl,rfl⟩ := run
        have condExact := counted_scalar_condition_error production source rel ranged words condition scalar condRanged condRun
        have condFinite : @evalHOLFinite 64 σ _ source
            (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = none := condExact
        apply errorLeaf production source rel ranged words (.while condition body) 0
        · simp only [progToHOL]
          rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
        · simp only [progToHOL]
          rw [controlSteps_while,condExact]
          rfl
      | some pair =>
        rcases pair with ⟨word,condCost⟩
        obtain ⟨condExact,costEq⟩ := counted_condition_invert production source rel ranged condition condRanged word condCost condRun
        subst condCost
        have condFinite : @evalHOLFinite 64 σ _ source
            (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = some (.val (.word word)) := condExact
        by_cases zero : word = 0
        · simp [condRun,zero] at run
          obtain ⟨rfl,rfl⟩ := run
          have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
          refine ⟨none,source,?_,?_,?_,?_⟩
          · simp only [progToHOL]
            rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
            simp [zero]
          · apply CountedOutcome.normal
            · simpa [clockEq] using rel
            · simpa [clockEq] using ranged
            · exact words
          · simp only [progToHOL]
            rw [controlSteps_while]
            simp [condExact,zero,countedErrorBonus]
          · omega
        · have zeroBits : word ≠ (0#64) := by simpa using zero
          let _ : DecidablePred source.decClockHOLFinite.memaddrs := dec
          cases bodyRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
              production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
              production.locals production.globals production.memory production.ffi body
              (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
          | none => simp [condRun,zeroBits,bodyRun] at run
          | some pair =>
            rcases pair with ⟨bodyResult,bodyCost⟩
            cases bodyResult with
            | normal l g m f =>
              cases restRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
                  production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel l g m f (.while condition body)
                  (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
              | none => simp [condRun,zeroBits,bodyRun,restRun] at run
              | some pair =>
                rcases pair with ⟨restResult,restCost⟩
                simp [condRun,zeroBits,bodyRun,restRun] at run
                obtain ⟨rfl,rfl⟩ := run
                have positive : source.clock ≠ 0 := by omega
                let entry := {production with clock := production.clock - 1}
                have entryRel : PanSemStateRelExec entry source.decClockHOLFinite.toExact := by
                  simpa [entry,decClockHOLFinite,decClockHOLExact] using rel.decClock
                have entryRanged : PanSemStateRelExecRanged entry := PanSemStateRelExecRanged.setClock ranged _
                have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
                    entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
                    (memoryAccess := some (panSemBitVec64MemoryAccess entry)) (contracts := contracts) = some (.normal l g m f,bodyCost) := by
                  simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
                obtain ⟨_,middle,holBody,outcome,bodyVisit,bodyClock⟩ := bodyBound entry source.decClockHOLFinite entryRel entryRanged words bodyRanged
                  context primitive handler functions fuel bodyCost (.normal l g m f) entryRun (by simp [decClockHOLFinite]; omega) (by omega) codeOk
                simp only [countedErrorBonus,Nat.add_zero] at bodyVisit
                cases outcome with
                | normal _ _ _ _ _ nextRel nextRanged nextWords =>
                  have memEq : middle.memaddrs = source.memaddrs := by
                    funext address
                    apply propext
                    exact (nextRel.2.2.2.2.2.2.1 address).symm.trans (rel.2.2.2.2.2.2.1 address)
                  let _ : DecidablePred middle.memaddrs := by rw [memEq]; exact dec
                  let next := {production with locals := l, globals := g, memory := m, ffi := f, clock := middle.clock}
                  have nextRun : evalPanValueFfiProgSteps context primitive handler next.structs functions next.baseAddress next.topAddress
                      panSemBitVec64BytesInWord fuel next.locals next.globals next.memory next.ffi (.while condition body)
                      (memoryAccess := some (panSemBitVec64MemoryAccess next)) (contracts := contracts) = some (restResult,restCost) := by
                    simpa [next,panSemBitVec64MemoryAccess] using restRun
                  obtain ⟨holResult,final,holRest,restOutcome,restVisit,restClock⟩ := ih next middle nextRel nextRanged nextWords byteRanged
                    context primitive handler functions restCost restResult nextRun (by simp [decClockHOLFinite] at bodyClock; omega) (by omega) codeOk
                  simp only [progToHOL] at holRest restVisit
                  refine ⟨holResult,final,?_,?_,?_,?_⟩
                  · simp only [progToHOL]
                    rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
                    simp [zeroBits,positive,holBody,holRest]
                  · exact outcomeRebase production l g m f middle.clock restOutcome
                  · simp only [progToHOL]
                    rw [controlSteps_while]
                    simp only [condExact,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨zero,positive⟩),holBody]
                    change 1 + (controlSteps (progToHOL body) source.decClockHOLFinite +
                      controlSteps (.while (expToHOL condition) (progToHOL body)) middle) ≤ _
                    omega
                  · simp [decClockHOLFinite] at bodyClock
                    omega
            | returned l g m f values =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have positive : source.clock ≠ 0 := by omega
              let entry := {production with clock := production.clock - 1}
              have entryRel : PanSemStateRelExec entry source.decClockHOLFinite.toExact := by
                simpa [entry,decClockHOLFinite,decClockHOLExact] using rel.decClock
              have entryRanged : PanSemStateRelExecRanged entry := PanSemStateRelExecRanged.setClock ranged _
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
                  entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry)) (contracts := contracts) = some (.returned l g m f values,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨holResult,final,holBody,outcome,bodyVisit,bodyClock⟩ := bodyBound entry source.decClockHOLFinite entryRel entryRanged words bodyRanged
                context primitive handler functions fuel bodyCost (.returned l g m f values) entryRun (by simp [decClockHOLFinite]; omega) (by omega) codeOk
              refine ⟨holResult,final,?_,?_,?_,?_⟩
              · simp only [progToHOL]
                rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
                cases outcome
                simp [zeroBits,positive,holBody]
              · exact outcomeRebase production production.locals production.globals production.memory production.ffi (production.clock-1) outcome
              · simp only [progToHOL]
                rw [controlSteps_while]
                simp only [condExact,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨zero,positive⟩),holBody]
                cases outcome
                simp only [Nat.add_zero]
                omega
              · simp [decClockHOLFinite] at bodyClock
                omega
            | error l g m f =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have positive : source.clock ≠ 0 := by omega
              let entry := {production with clock := production.clock - 1}
              have entryRel : PanSemStateRelExec entry source.decClockHOLFinite.toExact := by
                simpa [entry,decClockHOLFinite,decClockHOLExact] using rel.decClock
              have entryRanged : PanSemStateRelExecRanged entry := PanSemStateRelExecRanged.setClock ranged _
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
                  entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry)) (contracts := contracts) = some (.error l g m f,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨holResult,final,holBody,outcome,bodyVisit,bodyClock⟩ := bodyBound entry source.decClockHOLFinite entryRel entryRanged words bodyRanged
                context primitive handler functions fuel bodyCost (.error l g m f) entryRun (by simp [decClockHOLFinite]; omega) (by omega) codeOk
              simp only [countedErrorBonus] at bodyVisit
              refine ⟨holResult,final,?_,?_,?_,?_⟩
              · simp only [progToHOL]
                rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
                cases outcome
                simp [zeroBits,positive,holBody]
              · exact outcomeRebase production production.locals production.globals production.memory production.ffi (production.clock-1) outcome
              · simp only [progToHOL]
                rw [controlSteps_while]
                simp only [condExact,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨zero,positive⟩),holBody]
                cases outcome
                simp only [Nat.add_zero,countedErrorBonus]
                omega
              · simp [decClockHOLFinite] at bodyClock
                omega
            | raised l g m f e v =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              obtain ⟨_,_,_,outcome,_,_⟩ := bodyBound production source rel ranged words bodyRanged
                context primitive handler functions fuel bodyCost (.raised l g m f e v) bodyRun (by omega) (by omega) codeOk
              cases outcome
            | broke l g m f =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              obtain ⟨_,_,_,outcome,_,_⟩ := bodyBound production source rel ranged words bodyRanged
                context primitive handler functions fuel bodyCost (.broke l g m f) bodyRun (by omega) (by omega) codeOk
              cases outcome
            | finalFfi l g m f e =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              obtain ⟨_,_,_,outcome,_,_⟩ := bodyBound production source rel ranged words bodyRanged
                context primitive handler functions fuel bodyCost (.finalFfi l g m f e) bodyRun (by omega) (by omega) codeOk
              cases outcome
            | continued l g m f =>
              cases restRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
                  production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel l g m f (.while condition body)
                  (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) with
              | none => simp [condRun,zeroBits,bodyRun,restRun] at run
              | some pair =>
                rcases pair with ⟨restResult,restCost⟩
                simp [condRun,zeroBits,bodyRun,restRun] at run
                obtain ⟨rfl,rfl⟩ := run
                obtain ⟨_,_,_,outcome,_,_⟩ := bodyBound production source rel ranged words bodyRanged
                  context primitive handler functions fuel bodyCost (.continued l g m f) bodyRun (by omega) (by omega) codeOk
                cases outcome
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  exact loopAt fuel production source rel ranged words byteRanged context primitive handler functions count result run budget fuelBound codeOk

/-- A tail call reuses the smaller-fuel bridge of its resolved callee. -/
private theorem tailCallBridge {scope : List VarName} (name : FunName)
    (arguments : List (Exp (RiscV.Word 64)))
    (shape : ∀ e ∈ arguments, Scalar scope e)
    {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop}
    {contracts : Option PanValueCallContracts} {limit : Nat}
    (coherent : ∀ code functions, invariant code functions →
      ∃ exceptions, functions = countedFunctionsOfCode code ∧
        contracts = some (countedContractsOfCode code exceptions) ∧
        ∀ name entry, panSemCodeLookup code name = some entry → PanLangEntryByteRanged entry)
    (calleeBound : ∀ code functions, invariant code functions → ∀ structs name values body locals,
      panValueCallTarget structs contracts name functions values = some (body,locals) →
      Bridge invariant contracts limit body) :
    Bridge invariant contracts (limit+1) (.call none name arguments) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
  classical
  let _ : DecidablePred source.memaddrs := fun a => Classical.propDecidable (source.memaddrs a)
  have nameRanged : NameRanged name := byteRanged.1
  have exprRanged : ∀ e ∈ arguments, ExpByteRanged e := byteRanged.2.1
  obtain ⟨exceptions,funcEq,contractsEq,codeRanged⟩ := coherent production.code functions codeOk
  subst functions
  subst contracts
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    cases fuel with
    | zero => simp [evalPanValueFfiProgSteps,evalPanValueFfiCallSteps] at run
    | succ fuel =>
      simp only [evalPanValueFfiProgSteps,evalPanValueFfiCallSteps] at run
      have argsAgree := countedArguments_hol production source rel ranged arguments exprRanged
      cases argsRun : panValueCallArguments production.structs production.baseAddress production.topAddress
          panSemBitVec64BytesInWord production.locals production.globals production.memory arguments
          (some (panSemBitVec64MemoryAccess production)) with
      | none =>
        simp [argsRun] at run
        obtain ⟨rfl,rfl⟩ := run
        rw [argsRun] at argsAgree
        have argsExact : source.evalListHOLFinite (arguments.map expToHOL) = none := by simpa using argsAgree.symm
        apply errorLeaf production source rel ranged words (.call none name arguments) 1
        · simp only [progToHOL]
          rw [evaluateHOLFiniteState_call,argsExact]
        · simp only [progToHOL]
          rw [controlSteps.eq_def]
          simp only [argsExact]
      | some argPair =>
        rcases argPair with ⟨values,argCost⟩
        cases targetRun : panValueCallTarget production.structs
            (some (countedContractsOfCode production.code exceptions)) name (countedFunctionsOfCode production.code) values with
        | none =>
          simp [argsRun,targetRun] at run
          obtain ⟨rfl,rfl⟩ := run
          rw [argsRun] at argsAgree
          have argsExact : source.evalListHOLFinite (arguments.map expToHOL) = some (values.map panValueToHOL) := by
            simpa using argsAgree.symm
          have valuesWord := scalar_counted_arguments_words scope arguments shape production words values argCost (by
            simpa [panValueCallArguments] using argsRun)
          have valuesRanged : ∀ value ∈ values, PanValueByteRanged value := by
            intro value member
            obtain ⟨word,rfl⟩ := valuesWord value member
            simp [PanValueByteRanged]
          have lookup := countedCallTarget_hol production source rel exceptions name nameRanged values valuesRanged (codeRanged name)
          rw [targetRun] at lookup
          have lookupExact : lookupCodeHOLFinite source.code.lookup (ofString name) (values.map panValueToHOL) = none := by
            cases h : lookupCodeHOLFinite source.code.lookup (ofString name) (values.map panValueToHOL) <;> simp_all
          apply errorLeaf production source rel ranged words (.call none name arguments) (argCost+1)
          · simp only [progToHOL]
            rw [evaluateHOLFiniteState_call,argsExact]
            simp only
            rw [lookupExact]
          · simp only [progToHOL]
            rw [controlSteps.eq_def]
            simp only [argsExact,lookupExact]
        | some target =>
          obtain ⟨callee,calleeLocals⟩ := target
          obtain ⟨holBody,exactLocals,returnShape,argsExact,lookupExact,returnLookup,returnRanged,bodyEq,bodyRanged,
            entryRel,entryRanged,entryWords⟩ := countedCallEntry_rel production source rel ranged exceptions
              name nameRanged scope arguments shape exprRanged words values argCost argsRun (codeRanged name)
              callee calleeLocals targetRun
          let entry := {production with clock := production.clock-1, locals := calleeLocals}
          let exactEntry := callEntryStateHOLFinite source exactLocals
          let _ : DecidablePred exactEntry.memaddrs := dec
          have entryRel' : PanSemStateRelExec entry exactEntry.toExact := entryRel
          have entryRanged' : PanSemStateRelExecRanged entry := entryRanged
          have calleeBridge : Bridge invariant (some (countedContractsOfCode production.code exceptions)) limit callee := calleeBound production.code (countedFunctionsOfCode production.code) codeOk
            production.structs name values callee calleeLocals targetRun
          cases bodyRun : evalPanValueFfiProgSteps context primitive handler production.structs
              (countedFunctionsOfCode production.code) production.baseAddress production.topAddress
              panSemBitVec64BytesInWord fuel calleeLocals production.globals production.memory production.ffi callee
              (memoryAccess := some (panSemBitVec64MemoryAccess production))
              (contracts := some (countedContractsOfCode production.code exceptions)) with
          | none => simp [argsRun,targetRun,bodyRun] at run
          | some pair =>
            obtain ⟨bodyResult,bodyCost⟩ := pair
            cases bodyResult with
            | normal l g m f =>
              simp [argsRun,targetRun,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have positive : source.clock ≠ 0 := by omega
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs
                  (countedFunctionsOfCode entry.code) entry.baseAddress entry.topAddress panSemBitVec64BytesInWord
                  fuel entry.locals entry.globals entry.memory entry.ffi callee
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry))
                  (contracts := some (countedContractsOfCode production.code exceptions)) =
                    some (.normal l g m f,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨holResult,final,hol,outcome,visits,clock⟩ := calleeBridge entry exactEntry entryRel' entryRanged'
                entryWords bodyRanged context primitive handler (countedFunctionsOfCode entry.code) fuel bodyCost
                (.normal l g m f) entryRun (by simp [exactEntry,callEntryStateHOLFinite]; omega) (by omega) codeOk
              cases outcome with
              | normal l g m f final nextRel nextRanged nextWords =>
                dsimp [exactEntry] at hol visits clock
                refine ⟨some .error,final,?_,?_,?_,?_⟩
                · simp only [progToHOL]
                  rw [evaluateHOLFiniteState_call,argsExact]
                  simp only
                  rw [lookupExact]
                  simp [positive,bodyEq,hol]
                · exact .error l g m f final (by simpa [entry] using nextRel) (by simpa [entry] using nextRanged) nextWords
                · simp only [progToHOL]
                  rw [controlSteps_tailCall _ _ _ _ _ _ _ argsExact lookupExact positive]
                  simp only [bodyEq]
                  simp only [countedErrorBonus] at visits ⊢
                  omega
                · simp [callEntryStateHOLFinite] at clock
                  omega
            | returned l g m f returnedValues =>
              have costEq : count = argCost + bodyCost + 1 := by
                cases hv : panValueReturnValid production.structs
                    (some (countedContractsOfCode production.code exceptions)) name returnedValues <;>
                  simp [argsRun,targetRun,bodyRun,hv] at run <;> omega
              have positive : source.clock ≠ 0 := by omega
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs
                  (countedFunctionsOfCode entry.code) entry.baseAddress entry.topAddress panSemBitVec64BytesInWord
                  fuel entry.locals entry.globals entry.memory entry.ffi callee
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry))
                  (contracts := some (countedContractsOfCode production.code exceptions)) =
                    some (.returned l g m f returnedValues,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨holResult,final,hol,outcome,visits,clock⟩ := calleeBridge entry exactEntry entryRel' entryRanged'
                entryWords bodyRanged context primitive handler (countedFunctionsOfCode entry.code) fuel bodyCost
                (.returned l g m f returnedValues) entryRun (by simp [exactEntry,callEntryStateHOLFinite]; omega) (by omega) codeOk
              cases outcome with
              | returned l g m f word final nextRel nextRanged nextWords =>
                dsimp [exactEntry] at hol visits clock
                have valid : panValueReturnValid production.structs
                    (some (countedContractsOfCode production.code exceptions)) name [.word word] =
                    shapeEqHOL (shapeOfHOLExact (.val (.word word))) (shapeToHOL returnShape) := by
                  simp only [panValueReturnValid,returnLookup]
                  simp only [panValueShape,shapeOfHOLExact]
                  simpa [shapeToHOL] using panShapeMatches_eq_shapeEqHOL Shape.one returnShape (by simp [Flapjack.Pancake.PanLang.ShapeByteRanged]) returnRanged
                cases shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word word))) (shapeToHOL returnShape) with
                | false =>
                  have rejected : panValueReturnValid production.structs
                      (some (countedContractsOfCode production.code exceptions)) name [.word word] = false := valid.trans shapeOk
                  simp [argsRun,targetRun,bodyRun,rejected] at run
                  obtain ⟨rfl,rfl⟩ := run
                  refine ⟨some .error,final,?_,?_,?_,?_⟩
                  · simp only [progToHOL]
                    rw [evaluateHOLFiniteState_call,argsExact]
                    simp only
                    rw [lookupExact]
                    simp [positive,bodyEq,hol,shapeOk]
                  · exact .error l g m f final (by simpa [entry] using nextRel) (by simpa [entry] using nextRanged) nextWords
                  · simp only [progToHOL]
                    rw [controlSteps_tailCall _ _ _ _ _ _ _ argsExact lookupExact positive]
                    simp only [bodyEq,countedErrorBonus] at visits ⊢
                    omega
                  · simp [callEntryStateHOLFinite] at clock
                    omega
                | true =>
                  have accepted : panValueReturnValid production.structs
                      (some (countedContractsOfCode production.code exceptions)) name [.word word] = true := valid.trans shapeOk
                  simp [argsRun,targetRun,bodyRun,accepted] at run
                  obtain ⟨rfl,rfl⟩ := run
                  refine ⟨some (.returned (.val (.word word))),emptyLocalsHOLFinite final,?_,?_,?_,?_⟩
                  · simp only [progToHOL]
                    rw [evaluateHOLFiniteState_call,argsExact]
                    simp only
                    rw [lookupExact]
                    simp [positive,bodyEq,hol,shapeOk]
                  · apply CountedOutcome.returned
                    · simpa [entry,emptyLocalsHOLFinite,emptyLocalsHOLExact,PanSemStateFiniteExact.toExact] using nextRel.emptyLocals
                    · exact ⟨by simp,nextRanged.2.1,nextRanged.2.2⟩
                    · exact wordLocals_empty
                  · simp only [progToHOL]
                    rw [controlSteps_tailCall _ _ _ _ _ _ _ argsExact lookupExact positive]
                    simp only [bodyEq,countedErrorBonus] at visits ⊢
                    omega
                  · simp [callEntryStateHOLFinite] at clock
                    simpa [emptyLocalsHOLFinite] using (show source.clock ≤ final.clock + (argCost+bodyCost+1) by omega)
            | error l g m f =>
              simp [argsRun,targetRun,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have positive : source.clock ≠ 0 := by omega
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs
                  (countedFunctionsOfCode entry.code) entry.baseAddress entry.topAddress panSemBitVec64BytesInWord
                  fuel entry.locals entry.globals entry.memory entry.ffi callee
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry))
                  (contracts := some (countedContractsOfCode production.code exceptions)) =
                    some (.error l g m f,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨holResult,final,hol,outcome,visits,clock⟩ := calleeBridge entry exactEntry entryRel' entryRanged'
                entryWords bodyRanged context primitive handler (countedFunctionsOfCode entry.code) fuel bodyCost
                (.error l g m f) entryRun (by simp [exactEntry,callEntryStateHOLFinite]; omega) (by omega) codeOk
              cases outcome with
              | error l g m f final nextRel nextRanged nextWords =>
                dsimp [exactEntry] at hol visits clock
                refine ⟨some .error,emptyLocalsHOLFinite final,?_,?_,?_,?_⟩
                · simp only [progToHOL]
                  rw [evaluateHOLFiniteState_call,argsExact]
                  simp only
                  rw [lookupExact]
                  simp [positive,bodyEq,hol]
                · apply CountedOutcome.error
                  · simpa [entry,emptyLocalsHOLFinite,emptyLocalsHOLExact,PanSemStateFiniteExact.toExact] using nextRel.emptyLocals
                  · exact ⟨by simp,nextRanged.2.1,nextRanged.2.2⟩
                  · exact wordLocals_empty
                · simp only [progToHOL]
                  rw [controlSteps_tailCall _ _ _ _ _ _ _ argsExact lookupExact positive]
                  simp only [bodyEq]
                  simp only [countedErrorBonus] at visits ⊢
                  omega
                · simp [callEntryStateHOLFinite] at clock
                  simpa [emptyLocalsHOLFinite] using (show source.clock ≤ final.clock + (argCost+bodyCost+1) by omega)
            | raised l g m f e v =>
              by_cases exceptionOk : panValueExceptionValid production.structs
                  (some (countedContractsOfCode production.code exceptions)) e v = true
              · by_cases payloadOk : panValuePayloadWithinLimit production.structs v = true
                · simp [argsRun,targetRun,bodyRun,exceptionOk,payloadOk] at run
                  obtain ⟨rfl,rfl⟩ := run
                  have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs
                      (countedFunctionsOfCode entry.code) entry.baseAddress entry.topAddress panSemBitVec64BytesInWord
                      fuel entry.locals entry.globals entry.memory entry.ffi callee
                      (memoryAccess := some (panSemBitVec64MemoryAccess entry))
                      (contracts := some (countedContractsOfCode production.code exceptions)) =
                        some (.raised l g m f e v,bodyCost) := by
                    simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
                  obtain ⟨_,_,_,outcome,_,_⟩ := calleeBridge entry exactEntry entryRel' entryRanged'
                    entryWords bodyRanged context primitive handler (countedFunctionsOfCode entry.code) fuel bodyCost
                    (.raised l g m f e v) entryRun (by simp [exactEntry,callEntryStateHOLFinite]; omega) (by omega) codeOk
                  cases outcome
                · simp [argsRun,targetRun,bodyRun,exceptionOk,payloadOk] at run
              · simp [argsRun,targetRun,bodyRun,exceptionOk] at run
            | broke l g m f =>
              simp [argsRun,targetRun,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs
                  (countedFunctionsOfCode entry.code) entry.baseAddress entry.topAddress panSemBitVec64BytesInWord
                  fuel entry.locals entry.globals entry.memory entry.ffi callee
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry))
                  (contracts := some (countedContractsOfCode production.code exceptions)) =
                    some (.broke l g m f,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨_,_,_,outcome,_,_⟩ := calleeBridge entry exactEntry entryRel' entryRanged'
                entryWords bodyRanged context primitive handler (countedFunctionsOfCode entry.code) fuel bodyCost
                (.broke l g m f) entryRun (by simp [exactEntry,callEntryStateHOLFinite]; omega) (by omega) codeOk
              cases outcome
            | continued l g m f =>
              simp [argsRun,targetRun,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs
                  (countedFunctionsOfCode entry.code) entry.baseAddress entry.topAddress panSemBitVec64BytesInWord
                  fuel entry.locals entry.globals entry.memory entry.ffi callee
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry))
                  (contracts := some (countedContractsOfCode production.code exceptions)) =
                    some (.continued l g m f,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨_,_,_,outcome,_,_⟩ := calleeBridge entry exactEntry entryRel' entryRanged'
                entryWords bodyRanged context primitive handler (countedFunctionsOfCode entry.code) fuel bodyCost
                (.continued l g m f) entryRun (by simp [exactEntry,callEntryStateHOLFinite]; omega) (by omega) codeOk
              cases outcome
            | finalFfi l g m f e =>
              simp [argsRun,targetRun,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs
                  (countedFunctionsOfCode entry.code) entry.baseAddress entry.topAddress panSemBitVec64BytesInWord
                  fuel entry.locals entry.globals entry.memory entry.ffi callee
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry))
                  (contracts := some (countedContractsOfCode production.code exceptions)) =
                    some (.finalFfi l g m f e,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨_,_,_,outcome,_,_⟩ := calleeBridge entry exactEntry entryRel' entryRanged'
                entryWords bodyRanged context primitive handler (countedFunctionsOfCode entry.code) fuel bodyCost
                (.finalFfi l g m f e) entryRun (by simp [exactEntry,callEntryStateHOLFinite]; omega) (by omega) codeOk
              cases outcome

private theorem supportedBridge {invariant : PanSemCodeMap (RiscV.Word 64) → List (FunName × List VarName × Prog (RiscV.Word 64)) → Prop} {contracts : Option PanValueCallContracts} (limit : Nat) {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : Bridge invariant contracts limit program := by
  induction limit generalizing scope program with
  | zero =>
    intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget fuelBound codeOk
    have eq : fuel = 0 := by omega
    subst fuel
    simp [evalPanValueFfiProgSteps] at run
  | succ limit ih =>
    cases supported with
    | skip => exact skipBridge
    | assign name member scalar => exact assignBridge name scalar
    | decl name scalar shape => exact declBridge name scalar (ih shape)
    | seq a b => exact seqBridge (ih a) (ih b)
    | ite scalar a b => exact iteBridge scalar (ih a) (ih b)
    | «while» scalar body => exact whileBridge scalar (ih body)
    | ret scalar => exact returnBridge scalar

/-- A counted run of a supported body is a corresponding HOL run when the
source clock covers its explicitly given count. Clock consumption is bounded
by the count, and control visits by the count plus the error-result bonus. -/
theorem supported_counted_source {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (byteRanged : ProgByteRanged program) (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    {contracts : Option PanValueCallContracts}
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := contracts) = some (result,count))
    (budget : count ≤ source.clock) :
    ∃ holResult sourceFinal, source.evaluateHOLFiniteState (progToHOL program) = (holResult,sourceFinal) ∧
      CountedOutcome production result holResult sourceFinal ∧
      controlSteps (progToHOL program) source ≤ count + countedErrorBonus result ∧ source.clock ≤ sourceFinal.clock + count := by
  exact supportedBridge (invariant := fun _ _ => True) (contracts := contracts) fuel supported production source rel ranged words byteRanged
    context primitive handler functions fuel count result run budget (by rfl) trivial

end SteppedFlapjack.Concrete
