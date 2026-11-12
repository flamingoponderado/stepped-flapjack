import SteppedFlapjack.PanToCrepSteps.CountedAssign
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
/-- A successful global assignment, including a struct value, agrees with HOL and has an explicit visit bound. -/
theorem counted_assign_global {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (rel : PanSemStateRelExec production exact.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (expression : Exp (RiscV.Word 64)) (exprRanged : ExpByteRanged expression)
    (value : PanValue (RiscV.Word 64))
    (evaluated : evalPanSemStateExp production expression = some value)
    (valid : isValidValueHOLFinite exact .global (ofString name) (panValueToHOL value) = true)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + 1)
      production.locals production.globals production.memory production.ffi (.assign .global name expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal production.locals (updatePanValueMap production.globals name value) production.memory production.ffi,
          panValueExpStepCost expression + 1) ∧
    exact.evaluateHOLFiniteState (.assign .global (ofString name) (expToHOL expression)) =
      (none,PanSemStateFiniteExact.setGlobalHOLFinite (ofString name) (panValueToHOL value) exact) ∧
    PanSemStateRelExec {production with globals := updatePanValueMap production.globals name value}
      (PanSemStateFiniteExact.setGlobalHOLFinite (ofString name) (panValueToHOL value) exact).toExact ∧
    PanSemStateRelExecRanged {production with globals := updatePanValueMap production.globals name value} ∧
    controlSteps (.assign .global (ofString name) (expToHOL expression)) exact ≤ panValueExpStepCost expression + 1 := by
  have previous : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some value := by
    simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
  have counted : evalPanValueExpCounted production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (value,panValueExpStepCost expression) := by simp [evalPanValueExpCounted,previous]
  have vranged := evalPanSemStateExp_byteRanged production ranged expression exprRanged value evaluated
  have parity := panValueAssignmentValid_eq_isValidValueHOLFinite production exact rel ranged .global name nameRanged value vranged
  have prodValid : panValueAssignmentValid production.structs production.locals production.globals .global name value = true := by
    rw [parity]; exact valid
  have valueAgree := evalPanSemStateExp_agree production exact rel ranged expression exprRanged
  have exactEval : @evalHOLExact 64 σ _ exact.toExact
      (fun address => Classical.propDecidable (exact.memaddrs address)) (expToHOL expression) = some (panValueToHOL value) := by
    rw [evalHOLFinite_eq_classical,← valueAgree,evaluated]
    rfl
  refine ⟨?_,?_,PanSemStateRelExec.updateGlobals rel name nameRanged value,
    PanSemStateRelExecRanged.updateGlobals ranged name value vranged,?_⟩
  · simp [evalPanValueFfiProgSteps,panValueAssignGlobalResult,counted,prodValid]
  · rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign,exactEval]
    change (if exact.isValidValueHOLFinite .global (ofString name) (panValueToHOL value) = true then
      (none,setGlobalHOLFinite (ofString name) (panValueToHOL value) exact) else (some PanSemResultExact.error,exact)) = _
    simp only [valid,if_true]
  · rw [controlSteps.eq_def]
    simp only
    omega

end SteppedFlapjack.PanToCrepSteps
