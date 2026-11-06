import SteppedFlapjack.PanToCrepSteps.CountedReturn
import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge

/-! Counted local assignments and their exact HOL state updates. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A successful valid local assignment has the same updated state in the
executable and HOL semantics, and its actual counted statement-and-expression
cost bounds the HOL control visit. -/
theorem counted_assign_local {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (rel : PanSemStateRelExec production exact.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (expression : Exp (RiscV.Word 64)) (exprRanged : ExpByteRanged expression)
    (value : PanValue (RiscV.Word 64))
    (evaluated : evalPanSemStateExp production expression = some value)
    (valid : isValidValueHOLFinite exact .local (ofString name) (panValueToHOL value) = true)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + 1)
      production.locals production.globals production.memory production.ffi (.assign .local name expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal (updatePanValueMap production.locals name value) production.globals production.memory production.ffi,
          panValueExpStepCost expression + 1) ∧
    exact.evaluateHOLFiniteState (.assign .local (ofString name) (expToHOL expression)) =
      (none,PanSemStateFiniteExact.setVarHOLFinite (ofString name) (panValueToHOL value) exact) ∧
    PanSemStateRelExec {production with locals := updatePanValueMap production.locals name value}
      (PanSemStateFiniteExact.setVarHOLFinite (ofString name) (panValueToHOL value) exact).toExact ∧
    PanSemStateRelExecRanged {production with locals := updatePanValueMap production.locals name value} ∧
    controlSteps (.assign .local (ofString name) (expToHOL expression)) exact ≤ panValueExpStepCost expression + 1 := by
  have previous : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some value := by
    simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
  have counted : evalPanValueExpCounted production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (value,panValueExpStepCost expression) := by simp [evalPanValueExpCounted,previous]
  have vranged := evalPanSemStateExp_byteRanged production ranged expression exprRanged value evaluated
  have parity := panValueAssignmentValid_eq_isValidValueHOLFinite production exact rel ranged .local name nameRanged value vranged
  have prodValid : panValueAssignmentValid production.structs production.locals production.globals .local name value = true := by
    rw [parity]; exact valid
  have valueAgree := evalPanSemStateExp_agree production exact rel ranged expression exprRanged
  have exactEval : @evalHOLExact 64 σ _ exact.toExact
      (fun address => Classical.propDecidable (exact.memaddrs address)) (expToHOL expression) = some (panValueToHOL value) := by
    rw [evalHOLFinite_eq_classical,← valueAgree,evaluated]
    rfl
  refine ⟨?_,?_,PanSemStateRelExec.updateLocals rel name nameRanged value,
    PanSemStateRelExecRanged.updateLocals ranged name value vranged,?_⟩
  · simp [evalPanValueFfiProgSteps,panValueAssignLocalSteps,evalPanValueExpCountedWith,counted,prodValid]
  · rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign,exactEval]
    change (if exact.isValidValueHOLFinite .local (ofString name) (panValueToHOL value) = true then
      (none,setVarHOLFinite (ofString name) (panValueToHOL value) exact) else (some PanSemResultExact.error,exact)) = _
    simp only [valid,if_true]
  · rw [controlSteps.eq_def]
    simp only
    omega


/-- For any related executable and HOL states, a successful word-valued
return has the same result and its actual counted cost bounds the HOL visit. -/
theorem counted_return_word_related {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (rel : PanSemStateRelExec production exact.toExact) (ranged : PanSemStateRelExecRanged production)
    (expression : Exp (RiscV.Word 64)) (exprRanged : ExpByteRanged expression) (word : BitVec 64)
    (evaluated : evalPanSemStateExp production expression = some (.word word))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + 1)
      production.locals production.globals production.memory production.ffi (.return expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned (fun _ => none) production.globals production.memory production.ffi [.word word],
          panValueExpStepCost expression + 1) ∧
    exact.evaluateHOLFiniteState (.return (expToHOL expression)) =
      (some (.returned (.val (.word word))),emptyLocalsHOLFinite exact) ∧
    PanSemStateRelExec (panEmptyLocals production) (emptyLocalsHOLFinite exact).toExact ∧
    controlSteps (.return (expToHOL expression)) exact ≤ panValueExpStepCost expression + 1 := by
  have previous : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (.word word) := by
    simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
  have counted : evalPanValueExpCounted production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.word word,panValueExpStepCost expression) := by simp [evalPanValueExpCounted,previous]
  have valueAgree := evalPanSemStateExp_agree production exact rel ranged expression exprRanged
  have exactEval : @evalHOLExact 64 σ _ exact.toExact
      (fun address => Classical.propDecidable (exact.memaddrs address)) (expToHOL expression) =
        some (.val (.word word)) := by
    rw [evalHOLFinite_eq_classical,← valueAgree,evaluated]
    simp
  refine ⟨?_,?_,PanSemStateRelExec.emptyLocals rel,?_⟩
  · simp [evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,counted,
      panValuePayloadWithinLimit,panValuePayloadSizeFuel]
  · rw [evaluateHOLFiniteState_return,exactEval]
    simp [shapeOfHOLExact]
  · rw [controlSteps.eq_def]
    simp only
    omega


/-- A local assignment followed by a word return composes the actual counted
executions and bounds the two-statement HOL execution, carrying the updated
state from the first statement into the second. -/
theorem counted_assign_then_return {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (rel : PanSemStateRelExec production exact.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (assignment returned : Exp (RiscV.Word 64))
    (assignmentRanged : ExpByteRanged assignment) (returnedRanged : ExpByteRanged returned)
    (value : PanValue (RiscV.Word 64)) (word : BitVec 64)
    (evaluated : evalPanSemStateExp production assignment = some value)
    (valid : isValidValueHOLFinite exact .local (ofString name) (panValueToHOL value) = true)
    (returnEvaluated : evalPanSemStateExp
      {production with locals := updatePanValueMap production.locals name value} returned = some (.word word))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let post := setVarHOLFinite (ofString name) (panValueToHOL value) exact
    let sourceProgram := ProgHOL.seq (.assign .local (ofString name) (expToHOL assignment)) (.return (expToHOL returned))
    let cost := (panValueExpStepCost assignment + 1) + (panValueExpStepCost returned + 1) + 1
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + 2)
      production.locals production.globals production.memory production.ffi
      (.seq (.assign .local name assignment) (.return returned))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned (fun _ => none) production.globals production.memory production.ffi [.word word],cost) ∧
    exact.evaluateHOLFiniteState sourceProgram = (some (.returned (.val (.word word))),emptyLocalsHOLFinite post) ∧
    PanSemStateRelExec (panEmptyLocals {production with locals := updatePanValueMap production.locals name value})
      (emptyLocalsHOLFinite post).toExact ∧
    controlSteps sourceProgram exact ≤ cost := by
  let post := setVarHOLFinite (ofString name) (panValueToHOL value) exact
  let productionPost := {production with locals := updatePanValueMap production.locals name value}
  obtain ⟨firstExec,firstHol,postRel,postRanged,firstBound⟩ :=
    counted_assign_local production exact rel ranged name nameRanged assignment assignmentRanged value evaluated valid
      context primitive handler functions fuel
  let postDecidable : DecidablePred post.memaddrs := by
    change DecidablePred exact.memaddrs
    infer_instance
  obtain ⟨secondExec,secondHol,finalRel,secondBound⟩ :=
    @counted_return_word_related σ productionPost post postDecidable postRel postRanged returned returnedRanged word returnEvaluated
      context primitive handler functions fuel
  constructor
  · simp only [productionPost,panSemBitVec64MemoryAccess,evalPanValueFfiProgSteps] at secondExec
    simp only [panSemBitVec64MemoryAccess,evalPanValueFfiProgSteps] at firstExec
    simp [evalPanValueFfiProgSteps,panSemBitVec64MemoryAccess,firstExec,secondExec]
  · constructor
    · rw [evaluateHOLFiniteState_seq_line780,firstHol]
      exact secondHol
    · constructor
      · exact finalRel
      · rw [controlSteps_seq,firstHol]
        simp only
        dsimp only [post] at secondBound
        omega

end SteppedFlapjack.PanToCrepSteps
