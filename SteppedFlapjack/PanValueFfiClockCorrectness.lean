import Flapjack.PanValueFfiClockSemantics

/-!
# Named contracts for the clocked source semantics

These lemmas expose the clock and timeout behavior at the same boundaries as
CakeML's `panSem`: a `Tick` consumes one clock unit, a zero-clock tick times
out with cleared locals, a true zero-clock loop times out after evaluating its
condition, and ordinary leaf evaluation does not change the clock.
-/

namespace Flapjack

theorem panValueFfiClockTimeout_locals
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    (panValueFfiClockTimeout globals memory ffi clock).1 =
      .timeout (fun _ => none) globals memory ffi := by
  rfl

theorem evalPanValueFfiClockProg_tick_zero
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      .tick (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.timeout (fun _ => none) globals memory ffi, 0) := by
  simp [evalPanValueFfiClockProg, panValueFfiClockTimeout]

theorem evalPanValueFfiClockProg_tick_succ
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + 1) .tick (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg]

theorem evalPanValueFfiClockProg_while_zero_timeout
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) =
        some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) =
      some (.timeout (fun _ => none) globals memory ffi, 0) := by
  simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero,
    panValueFfiClockTimeout]

/-! A normal first component passes its complete state and remaining clock to
the second component.  This is the clocked counterpart of the sequencing rule
used by the source-to-Loop and Loop-to-Word simulation proofs. -/
theorem evalPanValueFfiClockProg_seq_normal
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
    (first second : Prog α) (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
        (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal middleLocals middleGlobals middleMemory middleFfi),
        firstClock))
    (hsecond : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
        middleFfi firstClock second (memoryAccess := memoryAccess)
        (contracts := contracts) = some (outcome, finalClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (outcome, finalClock) := by
  simp [evalPanValueFfiClockProg, hfirst, hsecond]

/- A raised first component terminates a sequence immediately.  The complete
   globals/memory/FFI state and exception payload are propagated unchanged;
   the second component is not evaluated. -/
theorem evalPanValueFfiClockProg_seq_raised
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock firstClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (middleLocals middleGlobals : VarName → Option (PanValue α))
    (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
    (first second : Prog α) (exception : ExceptionId) (value : PanValue α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
        (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised middleLocals middleGlobals middleMemory middleFfi
        exception value), firstClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.raised middleLocals middleGlobals middleMemory middleFfi
        exception value), firstClock) := by
  simp [evalPanValueFfiClockProg, hfirst]

/- A timeout in the first component also terminates a sequence immediately;
   its post-state and remaining clock are the exact Cake timeout payload. -/
theorem evalPanValueFfiClockProg_seq_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock firstClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (middleLocals middleGlobals : VarName → Option (PanValue α))
    (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
    (first second : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
        (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.timeout middleLocals middleGlobals middleMemory middleFfi, firstClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.timeout middleLocals middleGlobals middleMemory middleFfi, firstClock) := by
  simp [evalPanValueFfiClockProg, hfirst]

/-! A zero-clock call still evaluates its arguments and validates the callee
lookup/binding boundary before producing `TimeOut`.  This mirrors the order
of the corresponding `panSem` equation and prevents a timeout theorem from
silently accepting malformed calls. -/
theorem evalPanValueFfiClockCall_zero_timeout
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals : VarName → Option (PanValue α))
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      info function arguments (memoryAccess := memoryAccess)
      (contracts := contracts) =
      if panValueParametersValid structs contracts function values then
        some (.timeout (fun _ => none) globals memory ffi, 0)
      else some (.control (.error locals globals memory ffi), 0) := by
  by_cases hvalid : panValueParametersValid structs contracts function values = true
  · simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, hvalid, hargs, hlookup, hbind,
      panValueFfiClockTimeout]
  · simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, hvalid, hargs, hlookup]

/-! A successful nonzero-clock call returns the callee's final globals,
memory, FFI state, and remaining clock, while clearing the callee locals at
the caller boundary. -/
theorem evalPanValueFfiClockCall_returned_no_destination
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
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (_hwithin : panValueValuesWithinLimit structs values = true) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi values),
        finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hclock, hbody]

/-! An uncaught exception from a successful nonzero-clock call preserves the
callee's state and clock while clearing the callee locals at the caller
boundary. -/
theorem evalPanValueFfiClockCall_raised_no_handler
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
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised bodyLocals finalGlobals finalMemory finalFfi exception value),
        finalClock))
    (hwithin : panValuePayloadWithinLimit structs value = true) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value),
        finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hclock, hbody, hwithin]

/-! Cake's `pc_compile_correct[Call_Ret_TimeOut]` propagates a callee
timeout through a direct call.  The caller-local environment is cleared, but
the callee's globals, memory, FFI state, and remaining clock are retained. -/
theorem evalPanValueFfiClockCall_timeout
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
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.timeout bodyLocals finalGlobals finalMemory finalFfi, finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) finalGlobals finalMemory finalFfi, finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-! A declaration call propagates the callee's terminal outcomes.  Cake's
    `panSem` does not turn a callee timeout or FinalFFI into an evaluator
    failure merely because the call has a local continuation. -/
theorem evalPanValueFfiClockProg_decCall_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments (preserveReturnLocals := true) =
      some (.timeout (fun _ => none) nextGlobals nextMemory nextFfi, callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.timeout (fun _ => none) nextGlobals nextMemory nextFfi, callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

theorem evalPanValueFfiClockProg_decCall_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments (preserveReturnLocals := true) =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! A successful `DecCall` installs the single returned value for its
    continuation, checks the declared shape, and restores the caller's old
    local binding after that continuation completes. -/
theorem evalPanValueFfiClockProg_decCall_returned
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (calleeLocals : VarName → Option (PanValue α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (value : PanValue α) (outcome : PanValueFfiClockOutcome α σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments (preserveReturnLocals := true) =
      some (.control (.returned calleeLocals nextGlobals nextMemory nextFfi [value]),
        callClock))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
      nextGlobals nextMemory nextFfi callClock body =
      some (outcome, finalClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (panValueFfiClockRestoreLocal name (locals name) outcome, finalClock) := by
  simp [evalPanValueFfiClockProg, hcall, hshape, hbody]

/-! A declaration call whose callee returns a value of the wrong shape is
    rejected with an explicit Error while preserving the callee's complete
    post-call state and clock, as HOL `evaluate` does in the `DecCall` clause. -/
theorem evalPanValueFfiClockProg_decCall_shape_mismatch
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (calleeLocals : VarName → Option (PanValue α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (value : PanValue α)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments (preserveReturnLocals := true) =
      some (.control (.returned calleeLocals nextGlobals nextMemory nextFfi [value]),
        callClock))
    (hshape : panShapeMatches (panValueShape structs value) shape = false) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.control (.error calleeLocals nextGlobals nextMemory nextFfi), callClock) := by
  simp [evalPanValueFfiClockProg, hcall, hshape]

/-! An uncaught exception from a clocked `DecCall` bypasses its local
    continuation and preserves the callee's post-call state and clock. -/
theorem evalPanValueFfiClockProg_decCall_raised
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments (preserveReturnLocals := true) =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.decCall name shape function arguments body) =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the direct `Call_Ret_FinalFFI` branch of Cake's
    `pc_compile_correct`. A direct call has no declaration continuation, so
    the callee's final FFI event is returned unchanged by the enclosing
    program evaluator. -/
theorem evalPanValueFfiClockProg_call_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      info function arguments =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call info function arguments) =
      some (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the direct `Call_Ret_TimeOut` branch of Cake's
    `pc_compile_correct`: a direct call propagates the callee timeout without
    introducing a declaration continuation. -/
theorem evalPanValueFfiClockProg_call_timeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      info function arguments =
      some (.timeout nextLocals nextGlobals nextMemory nextFfi, callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call info function arguments) =
      some (.timeout nextLocals nextGlobals nextMemory nextFfi, callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the standalone `Call_Ret_Return` branch of Cake's
    `pc_compile_correct`: with no destination or handler, a valid returned
    value crosses the program-call boundary unchanged. -/
theorem evalPanValueFfiClockProg_call_returned
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (arguments : List (Exp α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.returned (fun _ => none) nextGlobals nextMemory nextFfi values),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call none function arguments) =
      some (.control (.returned (fun _ => none) nextGlobals nextMemory nextFfi values),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the standalone uncaught `Call_Ret_Exception` branch of Cake's
    `pc_compile_correct`: without a handler, the callee's raised exception and
    post-call state cross the program-call boundary unchanged. -/
theorem evalPanValueFfiClockProg_call_raised
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (arguments : List (Exp α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call none function arguments) =
      some (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
        exception value), callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the destination-bearing `Call_Ret_Return` branch of Cake's
    `pc_compile_correct`: a returned value is installed in the caller's
    destination, while the callee memory, FFI state, and clock are retained. -/
theorem evalPanValueFfiClockProg_call_returned_destination
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (destination : Option (VarKind × VarName))
    (function : FunName) (arguments : List (Exp α))
    (assignedLocals assignedGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      (some (destination, none)) function arguments =
      some (.control (.normal assignedLocals assignedGlobals nextMemory nextFfi),
        callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call (some (destination, none)) function arguments) =
      some (.control (.normal assignedLocals assignedGlobals nextMemory nextFfi),
        callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! This is the handler-bearing `Call_Ret_Exception` branch of Cake's
    `pc_compile_correct`: a caught exception resumes the handler through the
    enclosing program-call constructor with the callee's post-call state. -/
theorem evalPanValueFfiClockProg_call_caught_handler
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (caught : ExceptionId) (handlerVariable : VarName)
    (handlerProgram : Prog α) (function : FunName) (arguments : List (Exp α))
    (outcome : PanValueFfiClockOutcome α σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments =
      some (outcome, callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call (some (none, some (caught, handlerVariable, handlerProgram)))
        function arguments) =
      some (outcome, callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! Cake's handler-bearing `Call_Ret_Exception` branch also carries the
    syntactic assignment destination of the call (the `SOME (rts, SOME ...)`
    shape).  The caught-handler path returns the handler result directly and
    never reads that destination, so the same program-level lift applies to the
    destination-bearing info. -/
theorem evalPanValueFfiClockProg_call_caught_handler_destination
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (destination : Option (VarKind × VarName))
    (caught : ExceptionId) (handlerVariable : VarName)
    (handlerProgram : Prog α) (function : FunName) (arguments : List (Exp α))
    (outcome : PanValueFfiClockOutcome α σ)
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      (some (destination, some (caught, handlerVariable, handlerProgram)))
      function arguments =
      some (outcome, callClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.call (some (destination, some (caught, handlerVariable, handlerProgram)))
        function arguments) =
      some (outcome, callClock) := by
  simp [evalPanValueFfiClockProg, hcall]

/-! A caught exception resumes the handler in the callee's final state and
remaining clock, rather than restoring the caller's pre-call globals or
memory. -/
theorem evalPanValueFfiClockCall_caught_handler
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
    (calleeLocals bodyLocals calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (caught : ExceptionId) (exception : ExceptionId) (value : PanValue α)
    (handlerVariable : VarName) (handlerProgram : Prog α)
    (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised bodyLocals calleeGlobals calleeMemory calleeFfi exception value),
        finalClock))
    (hcaught : caught = exception)
    (hwithin : panValuePayloadWithinLimit structs value = true)
    (hhandler : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory calleeFfi
      finalClock handlerProgram (memoryAccess := memoryAccess) (contracts := none) =
      some (outcome, finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := none) =
      some (outcome, finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hclock, hbody,
    hcaught, hhandler, hwithin]

/-! A successful returned value may be assigned to a caller local or global.
The assignment is checked by the source shape predicate and uses the
callee's final globals, while memory, FFI state, and clock are propagated. -/
theorem evalPanValueFfiClockCall_returned_destination
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
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (_hwithin : panValueValuesWithinLimit structs values = true)
    (hassign : assignPanValueCallResult locals finalGlobals destination values
      (structs := structs) = some (assignedLocals, assignedGlobals)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (some (destination, none)) function arguments
      (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.normal assignedLocals assignedGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget, Option.elim_some, hargs, hlookup, hbind, hclock, hbody,
    hassign]

/-! One true loop iteration consumes one clock unit before evaluating the body
and then resumes the loop with the body's resulting state and clock. -/
theorem evalPanValueFfiClockProg_while_normal_iteration
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
    (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hrest : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      bodyClock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) = some (outcome, finalClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (outcome, finalClock) := by
  simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero, hclock,
    hbody, hrest]

/-! The top-level clocked evaluator preserves an explicitly raised call result.
    Declaration elaboration, generated contracts, and the remaining clock stay
    visible premises, so this bridge does not fold timeout or FinalFFI into a
    generic control case. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_raised_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi clock entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall]

/-! Cross-clock form of the raised declaration-call bridge.  Cake's
    `evaluate_add_clock_eq` proof supplies the two call witnesses separately;
    this theorem lifts them through declaration elaboration without hiding the
    source state, raised payload, or returned clocks. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_raised_call_cross_clock
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock ck : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi clock entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock))
    (hcallShift : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi (clock + ck) entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock + ck)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock) ∧
    evalPanValueFfiClockProgram context initial (clock + ck) primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.raised (fun _ => none) globals memory ffi exception value),
        nextClock + ck) := by
  constructor
  · simp [evalPanValueFfiClockProgram, hdeclarations, hcall]
  · simp [evalPanValueFfiClockProgram, hdeclarations, hcallShift]

/-! General declaration-boundary clock shifting for a call result.  The
    outcome remains polymorphic so Return, Raise, Timeout, and FinalFFI are
    not conflated; each call evaluator equation and the declaration lookup
    premise stays explicit for the Cake top-level induction. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_call_cross_clock
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock ck : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi clock entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) = some (outcome, nextClock))
    (hcallShift : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi (clock + ck) entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) = some (outcome, nextClock + ck)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) = some (outcome, nextClock) ∧
    evalPanValueFfiClockProgram context initial (clock + ck) primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) = some (outcome, nextClock + ck) := by
  constructor
  · simp [evalPanValueFfiClockProgram, hdeclarations, hentry, hcall]
  · simp [evalPanValueFfiClockProgram, hdeclarations, hentry, hcallShift]

/-! The corresponding timeout bridge keeps zero-clock behavior explicit at the
    declaration/program boundary. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_timeout_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi clock entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.timeout (fun _ => none) globals memory ffi, nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall]

/-! The top-level clocked evaluator also preserves a terminal `FinalFFI`
    outcome from the selected call.  This is the declaration-boundary form of
    Cake's `pc_compile_correct[Call_FinalFFI]` case. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_finalFfi_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (event : FfiFinalEvent) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi clock entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi locals globals memory ffi event), nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall]

/-! A successful singleton return crosses the clocked declaration boundary only
    when Cake's entry shape accepts the returned value. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_returned_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α) (shape : Shape)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (value : PanValue α) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi clock entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock))
    (hentry : lookupInfo entry state.returnShapes = some shape)
    (hshape : panShapeMatches (panValueShape state.structs value) shape = true) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) =
      some (.control (.returned locals globals memory ffi [value]), nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall, hentry, hshape]

theorem evalPanValueFfiClockProgram_of_declarations_and_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcall : evalPanValueFfiClockProgramCodeCall context primitive handler state fuel state.globals state.memory initial.ffi clock entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) = some (outcome, nextClock)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) = some (outcome, nextClock) := by
  simp [evalPanValueFfiClockProgram, hdeclarations, hcall, hentry]

variable {α σ : Type}
variable [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α]
variable [HXor α α α] [ShiftLeft α] [ShiftRight α] [LT α]
variable [DecidableRel (fun left right : α => left < right)] [PanCmp α]

set_option linter.unusedSimpArgs false in
theorem evalPanValueFfiClock_clock_le (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) :
    (∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
        (ffi : FfiState σ) (clock : Nat)
        (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
        (function : FunName) (arguments : List (Exp α))
        (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
        (preserveReturnLocals : Bool)
        (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat),
        evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
          (preserveReturnLocals := preserveReturnLocals) =
          some (outcome, resultClock) → resultClock ≤ clock)
    ∧
    (∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
        (ffi : FfiState σ) (clock : Nat) (program : Prog α)
        (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
        (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat),
        evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock program
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) → resultClock ≤ clock) := by
  refine evalPanValueFfiClockCall.mutual_induct
    (motive1 := fun fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler preserveReturnLocals =>
      ∀ outcome resultClock,
        evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
          (preserveReturnLocals := preserveReturnLocals) =
          some (outcome, resultClock) → resultClock ≤ clock)
    (motive2 := fun fuel locals globals memory ffi clock program memoryAccess contracts memoryHandler =>
      ∀ outcome resultClock,
        evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress bytesInWord
          fuel locals globals memory ffi clock program
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
          some (outcome, resultClock) → resultClock ≤ clock)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- case1: Call fuel 0
    intro memoryAccess contracts memoryHandler preserveReturnLocals locals globals memory ffi clock info function arguments outcome resultClock hrun
    simp only [evalPanValueFfiClockCall] at hrun
    exact absurd hrun (by simp)
  · -- case2: Call fuel+1
    intro fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler preserveReturnLocals hbodyIH hhandlerIH outcome resultClock hrun
    simp only [evalPanValueFfiClockCall, panValueCallArgumentsValue,
      evalPanValueExpsWith_none, panValueCallTarget] at hrun
    cases hvalues : evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) with
    | none =>
      simp only [hvalues, Option.elim_none, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨_, hc⟩ := hrun; omega
    | some values =>
      simp only [hvalues, Option.elim_some] at hrun
      cases hlookup : lookupPanFunction function functions with
      | none =>
        simp only [hlookup, Option.elim_none] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨_, hc⟩ := hrun; omega
      | some pair =>
        obtain ⟨parameters, body⟩ := pair
        simp only [hlookup, Option.bind_eq_bind, Option.bind_some] at hrun
        by_cases hparams : panValueParametersValid structs contracts function values = true
        · simp only [hparams, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
          cases hbind : bindPanValueParameters parameters values with
          | none =>
            simp only [hbind, Option.elim_none] at hrun
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨_, hc⟩ := hrun; omega
          | some calleeLocals =>
            simp only [hbind, Option.elim_some] at hrun
            by_cases hclock : clock = 0
            · simp only [hclock, if_true, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨_, hc⟩ := hrun
              omega
            · simp only [hclock, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
              cases hcallee : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                  topAddress bytesInWord fuel calleeLocals globals memory ffi (decPanClock clock) body
                  (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
              | none => simp only [hcallee, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
              | some pair2 =>
                obtain ⟨calleeOutcome, calleeClock⟩ := pair2
                simp only [hcallee, Option.bind_eq_bind, Option.bind_some] at hrun
                have hb : calleeClock ≤ decPanClock clock := hbodyIH body calleeLocals calleeOutcome calleeClock hcallee
                have hdc : decPanClock clock ≤ clock := Nat.sub_le clock 1
                cases calleeOutcome with
                | timeout l g m f =>
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨_, hc⟩ := hrun; omega
                | control result =>
                  cases result with
                  | normal l g m f =>
                    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨_, hc⟩ := hrun; omega
                  | broke l g m f =>
                    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨_, hc⟩ := hrun; omega
                  | continued l g m f =>
                    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨_, hc⟩ := hrun; omega
                  | returned l g m f vs =>
                    cases info with
                    | none =>
                      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                      obtain ⟨_, hc⟩ := hrun; omega
                    | some ipair =>
                      obtain ⟨destination, sndOpt⟩ := ipair
                      simp only [Option.bind_eq_bind, Option.bind_some] at hrun
                      cases hassign : assignPanValueCallResult locals g destination vs structs with
                      | none => simp only [hassign, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                      | some apair =>
                        simp only [hassign, Option.bind_eq_bind, Option.bind_some] at hrun
                        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                        obtain ⟨_, hc⟩ := hrun; omega
                  | raised l g m f ex v =>
                    by_cases hexc : (panValueExceptionValid structs contracts ex v && panValuePayloadWithinLimit structs v) = true
                    · simp only [hexc, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                      cases info with
                      | none =>
                        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                        obtain ⟨_, hc⟩ := hrun; omega
                      | some ipair =>
                        obtain ⟨destination, sndOpt⟩ := ipair
                        cases sndOpt with
                        | none =>
                          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                          obtain ⟨_, hc⟩ := hrun; omega
                        | some htriple =>
                          obtain ⟨caught, handlerVariable, handlerProgram⟩ := htriple
                          by_cases hcaught : (caught == ex) = true
                          · simp only [hcaught, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                            by_cases hvalid : panValueHandlerValid structs contracts locals handlerVariable v = true
                            · simp only [hvalid, if_true] at hrun
                              have hh : calleeClock ≤ calleeClock := by omega
                              have := hhandlerIH calleeClock g m f v handlerVariable handlerProgram outcome resultClock hrun
                              omega
                            · simp only [hvalid, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                          · simp only [hcaught, if_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                            obtain ⟨_, hc⟩ := hrun; omega
                    · simp only [hexc, if_false, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                  | finalFfi l g m f ev =>
                    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨_, hc⟩ := hrun; omega
                  | error l g m f =>
                    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨_, hc⟩ := hrun; omega
        · simp only [hparams, if_false, Option.elim_none] at hrun
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
  · -- case3: Prog fuel 0
    intro memoryAccess contracts memoryHandler locals globals memory ffi clock program outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    exact absurd hrun (by simp)
  · -- case4: Prog dec
    intro fuel locals globals memory ffi clock name shape value body memoryAccess contracts memoryHandler hbodyIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hvalue : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord value
        (memoryAccess := memoryAccess) with
    | none =>
      simp only [panValueDecAcceptedValue, evalPanValueExpWith_none, hvalue, Option.elim_none] at hrun
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨_, hc⟩ := hrun; omega
    | some valueResult =>
      simp only [panValueDecAcceptedValue, evalPanValueExpWith_none, hvalue] at hrun
      by_cases hmatch : panShapeMatches (panValueShape structs valueResult) shape = true
      · simp only [hmatch, if_true, Option.elim_some, Option.bind_eq_bind, Option.bind_some] at hrun
        cases hbody : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
            bytesInWord fuel (updatePanValueMap locals name valueResult) globals memory ffi clock body
            (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
        | none => simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
        | some pair =>
          obtain ⟨bodyOutcome, bodyClock⟩ := pair
          simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
          have hb : bodyClock ≤ clock := hbodyIH valueResult bodyOutcome bodyClock hbody
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
      · simp only [hmatch, if_false, Option.elim_none] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨_, hc⟩ := hrun; omega
  · -- case5: Prog seq
    intro fuel locals globals memory ffi clock first second memoryAccess contracts memoryHandler hfirstIH hsecondIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hfirst : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock first
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
    | none => simp only [hfirst, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some pair =>
      obtain ⟨firstOutcome, firstClock⟩ := pair
      simp only [hfirst, Option.bind_eq_bind, Option.bind_some] at hrun
      have hf : firstClock ≤ clock := hfirstIH firstOutcome firstClock hfirst
      cases firstOutcome with
      | timeout l g m f =>
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨_, hc⟩ := hrun; omega
      | control result =>
        cases result with
        | normal nl ng nm nf =>
          cases hsecond : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
              bytesInWord fuel nl ng nm nf firstClock second
              (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
          | none => simp only [hsecond, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
          | some pair2 =>
            obtain ⟨secondOutcome, secondClock⟩ := pair2
            simp only [hsecond, Option.bind_eq_bind, Option.bind_some] at hrun
            have hs : secondClock ≤ firstClock := hsecondIH firstClock nl ng nm nf secondOutcome secondClock hsecond
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨_, hc⟩ := hrun; omega
        | returned l g m f vs =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
        | raised l g m f ex v =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
        | broke l g m f =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
        | continued l g m f =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
        | finalFfi l g m f ev =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
        | error l g m f =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
  · -- case6: Prog ite
    intro fuel locals globals memory ffi clock condition thenBranch elseBranch memoryAccess contracts memoryHandler hthenIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcond : panValueIteConditionValue structs baseAddress topAddress bytesInWord
        locals globals memory condition memoryAccess with
    | none =>
      simp only [hcond, Option.elim_none] at hrun
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨_, hc⟩ := hrun; omega
    | some w =>
      simp only [hcond, Option.elim_some] at hrun
      exact hthenIH w outcome resultClock hrun
  · -- case7: Prog call
    intro fuel locals globals memory ffi clock info function arguments memoryAccess contracts memoryHandler hcallIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    exact hcallIH outcome resultClock hrun
  · -- case8: Prog decCall
    intro fuel locals globals memory ffi clock name shape function arguments body memoryAccess contracts memoryHandler hcallIH hbodyIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hcall : evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock none function arguments
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
        (preserveReturnLocals := true) with
    | none => simp only [hcall, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
    | some pair =>
      obtain ⟨callOutcome, nextClock⟩ := pair
      simp only [hcall, Option.bind_eq_bind, Option.bind_some] at hrun
      have hc : nextClock ≤ clock := hcallIH callOutcome nextClock hcall
      cases callOutcome with
      | timeout l g m f =>
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨_, he⟩ := hrun; omega
      | control result =>
        cases result with
        | returned l g m f vs =>
          cases vs with
          | nil =>
            simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
          | cons v rest =>
            cases rest with
            | cons v2 rest2 =>
              simp only [Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
            | nil =>
              simp only [Option.bind_eq_bind, Option.bind_some] at hrun
              by_cases hmatch : panShapeMatches (panValueShape structs v) shape = true
              · simp only [hmatch, if_true, Option.bind_eq_bind, Option.bind_some] at hrun
                cases hbody : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
                    bytesInWord fuel (updatePanValueMap locals name v) g m f nextClock body
                    (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
                | none => simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                | some pair2 =>
                  obtain ⟨bodyOutcome, bodyClock⟩ := pair2
                  simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
                  have hb : bodyClock ≤ nextClock := hbodyIH nextClock g m f v bodyOutcome bodyClock hbody
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨_, he⟩ := hrun; omega
              · simp only [hmatch, if_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨_, he⟩ := hrun; omega
        | normal l g m f =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, he⟩ := hrun; omega
        | broke l g m f =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, he⟩ := hrun; omega
        | continued l g m f =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, he⟩ := hrun; omega
        | raised l g m f ex v =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, he⟩ := hrun; omega
        | finalFfi l g m f ev =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, he⟩ := hrun; omega
        | error l g m f =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, he⟩ := hrun; omega
  · -- case9: Prog while
    intro fuel locals globals memory ffi clock conditionExp body memoryAccess contracts memoryHandler hbodyIH hrecIH outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    cases hv : panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
        memory conditionExp (memoryAccess := memoryAccess) with
    | none =>
      simp only [hv, Option.elim_none] at hrun
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨_, hc⟩ := hrun; omega
    | some w =>
      simp only [hv, Option.elim_some] at hrun
      by_cases hz : (w == 0) = true
      · simp only [hz, if_true, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨_, hc⟩ := hrun; omega
      · simp only [hz, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
        by_cases hclock : (clock == 0) = true
        · simp only [hclock, if_true, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, hc⟩ := hrun; omega
        · simp only [hclock, if_false, Option.bind_eq_bind, Option.bind_some] at hrun
          cases hbody : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
              bytesInWord fuel locals globals memory ffi (decPanClock clock) body
              (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
          | none => simp only [hbody, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
          | some pair =>
            obtain ⟨bodyOutcome, bodyClock⟩ := pair
            simp only [hbody, Option.bind_eq_bind, Option.bind_some] at hrun
            have hb : bodyClock ≤ decPanClock clock := hbodyIH bodyOutcome bodyClock hbody
            have hdc : decPanClock clock ≤ clock := Nat.sub_le clock 1
            cases bodyOutcome with
            | timeout l g m f =>
              simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨_, hc⟩ := hrun; omega
            | control result =>
              cases result with
              | normal nl ng nm nf =>
                cases hrec : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                    topAddress bytesInWord fuel nl ng nm nf bodyClock (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
                | none => simp only [hrec, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                | some pair2 =>
                  obtain ⟨recOutcome, recClock⟩ := pair2
                  simp only [hrec, Option.bind_eq_bind, Option.bind_some] at hrun
                  have hr : recClock ≤ bodyClock := hrecIH bodyClock nl ng nm nf recOutcome recClock hrec
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨_, hc⟩ := hrun; omega
              | continued nl ng nm nf =>
                cases hrec : evalPanValueFfiClockProg context primitive handler structs functions baseAddress
                    topAddress bytesInWord fuel nl ng nm nf bodyClock (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) with
                | none => simp only [hrec, Option.bind_eq_bind, Option.bind_none] at hrun; exact absurd hrun (by simp)
                | some pair2 =>
                  obtain ⟨recOutcome, recClock⟩ := pair2
                  simp only [hrec, Option.bind_eq_bind, Option.bind_some] at hrun
                  have hr : recClock ≤ bodyClock := hrecIH bodyClock nl ng nm nf recOutcome recClock hrec
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨_, hc⟩ := hrun; omega
              | broke nl ng nm nf =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨_, hc⟩ := hrun; omega
              | returned l g m f vs =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨_, hc⟩ := hrun; omega
              | raised l g m f ex v =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨_, hc⟩ := hrun; omega
              | finalFfi l g m f ev =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨_, hc⟩ := hrun; omega
              | error nl ng nm nf =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨_, hc⟩ := hrun; omega
  · -- case10: Prog tick clock 0
    intro memoryAccess contracts memoryHandler _fuel locals globals memory ffi outcome resultClock hrun
    simp only [evalPanValueFfiClockProg] at hrun
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨_, hc⟩ := hrun; omega
  · -- case11: Prog tick clock != 0
    intro memoryAccess contracts memoryHandler _fuel locals globals memory ffi clock hclock outcome resultClock hrun
    simp only [evalPanValueFfiClockProg, if_neg hclock, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨_, hc⟩ := hrun
    have hdc : decPanClock clock ≤ clock := Nat.sub_le clock 1
    omega
  · -- case12: Prog fallback (leaf)
    intro _fuel locals globals memory ffi clock program memoryAccess contracts memoryHandler hdec hseq hite hcall hdecCall hwhile htick outcome resultClock hrun
    simp only [evalPanValueFfiClockProg, hdec, hseq, hite, hcall, hdecCall, hwhile, htick, evalPanValueFfiClockLeaf, Function.comp_def] at hrun
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨_, _, heq⟩ := hrun
    injection heq with _ h2
    omega

/-- The program-level corollary: a successful clocked program run never returns a clock above its input clock. -/
theorem evalPanValueFfiClockProg_clock_le (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α) (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (clock : Nat) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat)
    (hrun : evalPanValueFfiClockProg context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock program
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler) =
        some (outcome, resultClock)) : resultClock ≤ clock :=
  (evalPanValueFfiClock_clock_le context primitive handler structs functions baseAddress topAddress
    bytesInWord).2 fuel locals globals memory ffi clock program memoryAccess contracts memoryHandler
    outcome resultClock hrun

/-- The call-level corollary: a successful clocked call never returns a clock above its input clock. -/
theorem evalPanValueFfiClockCall_clock_le (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α) (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (preserveReturnLocals : Bool)
    (outcome : PanValueFfiClockOutcome α σ) (resultClock : Nat)
    (hrun : evalPanValueFfiClockCall context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock info function arguments
        (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
        (preserveReturnLocals := preserveReturnLocals) =
        some (outcome, resultClock)) : resultClock ≤ clock :=
  (evalPanValueFfiClock_clock_le context primitive handler structs functions baseAddress topAddress
    bytesInWord).1 fuel locals globals memory ffi clock info function arguments memoryAccess contracts
    memoryHandler preserveReturnLocals outcome resultClock hrun

end Flapjack
