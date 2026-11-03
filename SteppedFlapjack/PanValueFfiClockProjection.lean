import Flapjack.PanValueFfiClockCorrectness
import SteppedFlapjack.PanValueFfiSemantics

/-!
# Clocked-to-stepped source projection

This file provides the first compositional bridge between the explicit-clock
stateful-FFI evaluator and the source-step evaluator.  The hypotheses expose
the agreement at the two component boundaries; the conclusion preserves both
the clocked result and the exact accumulated source-step count across `seq`.
-/

namespace Flapjack

/-- The compatibility step evaluator has no clock: at zero clock, `Tick`
     succeeds there while the clocked evaluator times out. Consequently a
     clocked-to-stepped correspondence needs a non-timeout condition or a
     clock-aware step relation. This is Flapjack-specific infrastructure,
     not a port of a HOL declaration. -/
theorem tick_zero_clocked_and_stepped_differ
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0 .tick =
      some (.timeout (fun _ => none) globals memory ffi, 0) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi .tick =
      some (.normal locals globals memory ffi, 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, panValueFfiClockTimeout]
  · simp [evalPanValueFfiProgSteps]

/-! A named source-side view of a clocked result.  This is deliberately a
    structural projection rather than a quotient: every source state field,
    FFI terminal event, and the remaining clock stays observable.  In
    particular, `timeout` is not conflated with a normal control result. -/
inductive PanValueFfiClockResultProjection (α : Type u) (σ : Type v) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
  | error (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (values : List (PanValue α)) (clock : Nat)
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (exception : ExceptionId) (value : PanValue α) (clock : Nat)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
  | timeout (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
  | finalFfi (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (event : FfiFinalEvent) (clock : Nat)

def panValueFfiClockResultProjection :
    PanValueFfiClockResult α σ → PanValueFfiClockResultProjection α σ
  | (.control (.normal locals globals memory ffi), clock) =>
      .normal locals globals memory ffi clock
  | (.control (.error locals globals memory ffi), clock) =>
      .error locals globals memory ffi clock
  | (.control (.returned locals globals memory ffi values), clock) =>
      .returned locals globals memory ffi values clock
  | (.control (.raised locals globals memory ffi exception value), clock) =>
      .raised locals globals memory ffi exception value clock
  | (.control (.broke locals globals memory ffi), clock) =>
      .broke locals globals memory ffi clock
  | (.control (.continued locals globals memory ffi), clock) =>
      .continued locals globals memory ffi clock
  | (.timeout locals globals memory ffi, clock) =>
      .timeout locals globals memory ffi clock
  | (.control (.finalFfi locals globals memory ffi event), clock) =>
      .finalFfi locals globals memory ffi event clock

/-! Adding clock fuel changes only the observable remaining-clock field. -/
def panValueFfiClockResultProjection_shiftClock (extra : Nat) :
    PanValueFfiClockResultProjection α σ →
      PanValueFfiClockResultProjection α σ
  | .normal locals globals memory ffi clock =>
      .normal locals globals memory ffi (clock + extra)
  | .error locals globals memory ffi clock =>
      .error locals globals memory ffi (clock + extra)
  | .returned locals globals memory ffi values clock =>
      .returned locals globals memory ffi values (clock + extra)
  | .raised locals globals memory ffi exception value clock =>
      .raised locals globals memory ffi exception value (clock + extra)
  | .broke locals globals memory ffi clock =>
      .broke locals globals memory ffi (clock + extra)
  | .continued locals globals memory ffi clock =>
      .continued locals globals memory ffi (clock + extra)
  | .timeout locals globals memory ffi clock =>
      .timeout locals globals memory ffi (clock + extra)
  | .finalFfi locals globals memory ffi event clock =>
      .finalFfi locals globals memory ffi event (clock + extra)

theorem panValueFfiClockResultProjection_finalFfi
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (event : FfiFinalEvent) (clock : Nat) :
    panValueFfiClockResultProjection
      (.control (.finalFfi locals globals memory ffi event), clock) =
      .finalFfi locals globals memory ffi event clock := by
  rfl

theorem panValueFfiClockResultProjection_timeout
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    panValueFfiClockResultProjection
      (.timeout locals globals memory ffi, clock) =
      .timeout locals globals memory ffi clock := by
  rfl

theorem panValueFfiClockResultProjection_tick_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    (evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      .tick).map panValueFfiClockResultProjection =
      some (.timeout (fun _ => none) globals memory ffi 0) := by
  rw [evalPanValueFfiClockProg_tick_zero]
  rfl

theorem panValueFfiClockResultProjection_tick_succ
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    (evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + 1) .tick).map panValueFfiClockResultProjection =
      some (.normal locals globals memory ffi clock) := by
  rw [evalPanValueFfiClockProg_tick_succ]
  rfl

theorem evalPanValueFfiClockProg_seq_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock firstClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (middleLocals middleGlobals : VarName → Option (PanValue α))
    (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
    (secondResult : PanValueFfiControlResult α σ)
    (firstSteps secondSteps : Nat)
    (first second : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hfirstClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal middleLocals middleGlobals middleMemory middleFfi), firstClock))
    (hsecondClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
      middleFfi firstClock second (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control secondResult, finalClock))
    (hfirstSteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi first
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.normal middleLocals middleGlobals middleMemory middleFfi, firstSteps))
    (hsecondSteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
      middleFfi second (memoryAccess := memoryAccess) (contracts := contracts) =
      some (secondResult, secondSteps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control secondResult, finalClock) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (secondResult, firstSteps + secondSteps + 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, hfirstClock, hsecondClock]
  · simp [evalPanValueFfiProgSteps, hfirstSteps, hsecondSteps]

/-! The no-destination return branch has the same projection property at a
call boundary.  Argument steps and callee steps are added by the stepped
evaluator, while the clocked evaluator returns the callee's remaining clock. -/
theorem evalPanValueFfiClockCall_returned_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hreturn : panValueReturnValid structs contracts function values = true)
    (_hwithin : panValueValuesWithinLimit structs values = true)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned bodyLocals finalGlobals finalMemory finalFfi values, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi values),
        finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned (fun _ => none) finalGlobals finalMemory finalFfi values,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hparameters, hclock,
      hclockBody]
  · simp [evalPanValueFfiCallSteps, panValueCallArguments, panValueCallTarget, Option.elim_some, hargsSteps, hlookup, hbind, hparameters, hreturn,
      hstepBody]

/-! The uncaught-exception call branch projects in the same way: the callee
state and clock are preserved, and the source-step count includes argument
and callee evaluation. -/
theorem evalPanValueFfiClockCall_raised_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (exception : ExceptionId) (value : PanValue α)
    (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hexception : panValueExceptionValid structs contracts exception value = true)
    (hwithin : panValuePayloadWithinLimit structs value = true)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised bodyLocals finalGlobals finalMemory finalFfi exception value),
        finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.raised bodyLocals finalGlobals finalMemory finalFfi exception value, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value),
        finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hexception,
      hwithin, hclockBody]
  · simp [evalPanValueFfiCallSteps, panValueCallArguments, panValueCallTarget, Option.elim_some, hargsSteps, hlookup, hbind, hparameters, hexception,
      hwithin, hstepBody]

/-! Cake's `pc_compile_correct[Call_Ret_FinalFFI]` propagates a terminal FFI
event through a direct call without applying return or exception validation.
The clocked and stepped evaluators preserve the same post-state/event; only
their clock and step accounting differ. -/
theorem evalPanValueFfiClockCall_finalFfi_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (event : FfiFinalEvent) (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi bodyLocals finalGlobals finalMemory finalFfi event),
        finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.finalFfi bodyLocals finalGlobals finalMemory finalFfi event, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi (fun _ => none) finalGlobals finalMemory finalFfi event),
        finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.finalFfi (fun _ => none) finalGlobals finalMemory finalFfi event,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hparameters, hclock,
      hclockBody]
  · simp [evalPanValueFfiCallSteps, panValueCallArguments, panValueCallTarget, Option.elim_some, hargsSteps, hlookup, hbind, hparameters,
      hstepBody]

/-! Return values assigned to an explicit caller destination project as well.
The assignment result is shared by the clocked and stepped evaluators, while
the callee memory, FFI state, and remaining clock continue to be preserved. -/
theorem evalPanValueFfiClockCall_destination_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (destination : Option (VarKind × VarName))
    (assignedLocals assignedGlobals : VarName → Option (PanValue α))
    (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hreturn : panValueReturnValid structs contracts function values = true)
    (_hwithin : panValueValuesWithinLimit structs values = true)
    (hassign : assignPanValueCallResult locals finalGlobals destination values
      (structs := structs) = some (assignedLocals, assignedGlobals))
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned bodyLocals finalGlobals finalMemory finalFfi values, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (destination, none)) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal assignedLocals assignedGlobals finalMemory finalFfi), finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (some (destination, none)) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.normal assignedLocals assignedGlobals finalMemory finalFfi,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hparameters, hclock,
      hassign, hclockBody]
  · simp [evalPanValueFfiCallSteps, panValueCallArguments, panValueCallTarget, Option.elim_some, hargsSteps, hlookup, hbind, hparameters, hreturn,
      hassign, hstepBody]

/-! A caught exception projects through the handler continuation.  The
handler's clock and step result are both threaded after the callee's state has
been transferred to it. -/
theorem evalPanValueFfiClockCall_handler_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock bodyClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (caught exception : ExceptionId) (value : PanValue α)
    (handlerVariable : VarName) (handlerProgram : Prog α)
    (handlerResult : PanValueFfiControlResult α σ)
    (argumentSteps calleeSteps handlerSteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hexception : panValueExceptionValid structs contracts exception value = true)
    (hwithin : panValuePayloadWithinLimit structs value = true)
    (hcaught : caught = exception)
    (hhandlerValid : panValueHandlerValid structs contracts locals handlerVariable value = true)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised bodyLocals calleeGlobals calleeMemory calleeFfi exception value),
        bodyClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.raised bodyLocals calleeGlobals calleeMemory calleeFfi exception value,
        calleeSteps))
    (hclockHandler : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory calleeFfi
      bodyClock handlerProgram (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control handlerResult, finalClock))
    (hstepHandler : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory calleeFfi
      handlerProgram (memoryAccess := memoryAccess) (contracts := contracts) =
      some (handlerResult, handlerSteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control handlerResult, finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (handlerResult, argumentSteps + calleeSteps + handlerSteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hexception,
      hwithin, hcaught, hhandlerValid, hclockBody, hclockHandler]
  · simp [evalPanValueFfiCallSteps, panValueCallArguments, panValueCallTarget, Option.elim_some, hargsSteps, hlookup, hbind, hparameters, hexception,
      hwithin, hcaught, hhandlerValid, hstepBody, hstepHandler]

/-! One true loop iteration also projects compositionally.  The body consumes
one clock unit, and both evaluators then resume the loop from the body state. -/
theorem evalPanValueFfiClockProg_while_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock bodyClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α)) (bodyFfi : FfiState σ)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
    (finalResult : PanValueFfiControlResult α σ)
    (conditionSteps bodySteps restSteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionSteps : evalPanValueExpCounted structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue, conditionSteps))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : clock ≠ 0)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.normal bodyLocals bodyGlobals bodyMemory bodyFfi, bodySteps))
    (hclockRest : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      bodyClock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) = some (.control finalResult, finalClock))
    (hstepRest : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (finalResult, restSteps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control finalResult, finalClock) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (finalResult, conditionSteps + bodySteps + restSteps + 1) := by
  constructor
  · have hcond : panValueIteConditionValue structs baseAddress topAddress bytesInWord
        locals globals memory condition memoryAccess = some conditionValue := by
      simp [panValueIteConditionValue, hcondition]
    simp [evalPanValueFfiClockProg, hcond, hconditionNonzero, hclock,
      hclockBody, hclockRest]
  · have hcondSteps : panValueIteCondition structs baseAddress topAddress bytesInWord
        locals globals memory condition memoryAccess = some (conditionValue, conditionSteps) := by
      simp [panValueIteCondition, hconditionSteps]
    simp [evalPanValueFfiProgSteps, hcondSteps, hconditionNonzero,
      hstepBody, hstepRest]

/-! A declaration call projects through its returned-value continuation.  The
continuation receives the callee's state and clock, and the declaration's
shadowed local is restored in both result representations. -/
theorem evalPanValueFfiClockProg_decCall_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (callLocals callGlobals : VarName → Option (PanValue α))
    (callMemory : α → Option (PanValue α)) (callFfi : FfiState σ)
    (name : VarName) (shape : Shape) (value : PanValue α)
    (function : FunName) (arguments : List (Exp α)) (body : Prog α)
    (oldValue : Option (PanValue α))
    (clockBodyOutcome : PanValueFfiClockOutcome α σ)
    (stepBodyResult : PanValueFfiControlResult α σ)
    (callSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hcallClock : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock none function
      arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (preserveReturnLocals := true) =
      some (.control (.returned callLocals callGlobals callMemory callFfi [value]), callClock))
    (hcallSteps : evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi none function
      arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (preserveReturnLocals := true) =
      some (.returned callLocals callGlobals callMemory callFfi [value], callSteps))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hbodyClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
      callGlobals callMemory callFfi callClock body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (clockBodyOutcome, finalClock))
    (hbodySteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
      callGlobals callMemory callFfi body (memoryAccess := memoryAccess)
      (contracts := contracts) = some (stepBodyResult, bodySteps))
    (hold : locals name = oldValue) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (panValueFfiClockRestoreLocal name oldValue clockBodyOutcome, finalClock) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (restorePanValueFfiLocal name oldValue stepBodyResult,
        callSteps + bodySteps + 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, hcallClock, hshape, hbodyClock, hold]
  · simp [evalPanValueFfiProgSteps, hcallSteps, hshape, hbodySteps, hold]

end Flapjack
