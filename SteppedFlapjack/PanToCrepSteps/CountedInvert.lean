import SteppedFlapjack.PanToCrepSteps.CountedIte
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

/-- A counted skip yields the identical HOL state and bounds one visit. -/
theorem counted_skip_invert {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi .skip
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal production.locals production.globals production.memory production.ffi,count)) :
    source.evaluateHOLFiniteState .skip = (none,source) ∧ controlSteps .skip source ≤ count := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,Option.some.injEq,Prod.mk.injEq,true_and] at run
    subst count
    constructor
    · exact evaluateHOLFiniteState_skip source
    · rw [controlSteps.eq_def]
      simp

/-- A counted word-return reveals the corresponding HOL return and a source
control bound without assuming the expression result in advance. -/
theorem counted_return_invert {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (expression : Exp (RiscV.Word 64)) (exprRanged : ExpByteRanged expression) (word : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.return expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned (fun _ => none) production.globals production.memory production.ffi [.word word],count)) :
    source.evaluateHOLFiniteState (.return (expToHOL expression)) =
      (some (.returned (.val (.word word))),source.emptyLocalsHOLFinite) ∧
    PanSemStateRelExec (panEmptyLocals production) source.emptyLocalsHOLFinite.toExact ∧
    PanSemStateRelExecRanged (panEmptyLocals production) ∧
    controlSteps (.return (expToHOL expression)) source ≤ count := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,
      evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => simp [evaluated] at run
    | some value =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq,PanValueFfiControlResult.returned.injEq,List.cons.injEq,
          and_true,true_and] at run
        obtain ⟨rfl,rfl⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some (.word word) := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        have result := counted_return_word_related production source rel ranged expression exprRanged word expressionRun
          context primitive handler functions fuel
        obtain ⟨_,hol,finalRel,bound⟩ := result
        exact ⟨hol,finalRel,ranged.panEmptyLocals,bound⟩
      · simp at run
/-- A successful counted local assignment determines its HOL update,
related state and visit bound. -/
theorem counted_assign_invert {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (expression : Exp (RiscV.Word 64)) (exprRanged : ExpByteRanged expression)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (postLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.assign .local name expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal postLocals production.globals production.memory production.ffi,count)) :
    ∃ value, postLocals = updatePanValueMap production.locals name value ∧
      source.evaluateHOLFiniteState (.assign .local (ofString name) (expToHOL expression)) =
        (none,setVarHOLFinite (ofString name) (panValueToHOL value) source) ∧
      PanSemStateRelExec {production with locals := postLocals}
        (setVarHOLFinite (ofString name) (panValueToHOL value) source).toExact ∧
      PanSemStateRelExecRanged {production with locals := postLocals} ∧
      controlSteps (.assign .local (ofString name) (expToHOL expression)) source ≤ count := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,panValueAssignLocalSteps,evalPanValueExpCountedWith,
      evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => simp [evaluated] at run
    | some value =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq,PanValueFfiControlResult.normal.injEq,
          and_true] at run
        obtain ⟨postEq,rfl⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some value := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        have vranged := evalPanSemStateExp_byteRanged production ranged expression exprRanged value expressionRun
        have parity := panValueAssignmentValid_eq_isValidValueHOLFinite production source rel ranged .local name nameRanged value vranged
        have valid : isValidValueHOLFinite source .local (ofString name) (panValueToHOL value) = true := by
          rw [← parity]
          assumption
        have result := counted_assign_local production source rel ranged name nameRanged expression exprRanged value expressionRun valid
          context primitive handler functions fuel
        obtain ⟨_,hol,finalRel,finalRanged,bound⟩ := result
        exact ⟨value,postEq.symm,hol,by simpa [postEq] using finalRel,by simpa [postEq] using finalRanged,bound⟩
      · simp at run

/-- A successful counted condition determines the same HOL word and exact
expression cost. -/
theorem counted_condition_invert {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (condition : Exp (RiscV.Word 64)) (conditionRanged : ExpByteRanged condition) (word : BitVec 64) (cost : Nat)
    (run : panValueIteCondition production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
      production.locals production.globals production.memory condition
      (some (panSemBitVec64MemoryAccess production)) = some (word,cost)) :
    @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL condition) = some (.val (.word word)) ∧ cost = panValueExpStepCost condition := by
  simp only [panValueIteCondition,evalPanValueExpCounted] at run
  cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord condition
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
  | none => simp [evaluated] at run
  | some value =>
    cases value with
    | word bits =>
      simp only [evaluated,Option.map_some,Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      have expressionRun : evalPanSemStateExp production condition = some (.word bits) := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      exact ⟨(counted_condition_word production source rel ranged condition conditionRanged bits expressionRun).2,rfl⟩
    | rStruct fields => simp [evaluated] at run
    | nStruct name fields => simp [evaluated] at run

end SteppedFlapjack.PanToCrepSteps
