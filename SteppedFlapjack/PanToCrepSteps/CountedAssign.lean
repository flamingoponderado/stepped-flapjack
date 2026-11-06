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

end SteppedFlapjack.PanToCrepSteps
