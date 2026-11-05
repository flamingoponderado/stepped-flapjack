import SteppedFlapjack.PanValueFfiClockCorrectness

/-!
# Clock-shift prerequisite for the clocked stateful-FFI evaluators

Cake's `evaluate_add_clock_eq`
(`cakeml/pancake/semantics/panPropsScript.sml:698`) says that a successful
non-timeout run is unchanged when the input clock is increased by a constant,
with the result clock increased by the same constant.  Cake's evaluator only
decrements the clock on `While`/`Tick`/`Call`, so the shift commutes with
every clock decrement.

This file records the arithmetic fact that makes the same shift go through
for the structural-fuel-indexed clocked evaluator
(`Flapjack.PanValueFfiClockSemantics`): on a nonzero clock,
`decPanClock (clock + ck) = decPanClock clock + ck`.  It is the sole
clock-arithmetic obligation that a whole-program clock-shift theorem (the
mutually-recursive analogue of `evalPanValueFfiClock_clock_le`) needs, and it
is used to state where the missing whole-program invariant must come from.

Added while auditing Cake `evaluate_add_clock_eq` against the current
clocked evaluator; see `flapjack-pxn.11` for the structural-fuel adequacy
framework that the full shift invariant is gated on.

Direct source review of `panPropsScript.sml:698` `evaluate_add_clock_eq` and
`:724` `evaluate_clock_sub` (beads `flapjack-4ac.4.45` / `flapjack-4ac.4.46`)
confirms there is no statement-exact Lean counterpart.  The HOL statements
concern the exact `evaluate` relation over `panSem$state` with a `TimeOut`
side condition and the `dec_clock`/`state_component_equality` theory; the
clocked evaluator here (`PanValueFfiClockSemantics`) is a structural-fuel
indexed function over a different state and value model, and only its
clock-arithmetic core and selected `Tick`/`While` branches are proved.  A
faithful port needs the exact `evaluate` dispatcher over the exact `eval` and
the finite-support `panSem$state` carrier, tracked by
`flapjack-pxn.18.3.7.1.3.1.1.2` (state) and `flapjack-pxn.18.3.5.8`
(mlstring carriers), with the whole-program structural-fuel shift invariant
under `flapjack-pxn.11`.  The lemmas below remain Flapjack-specific
prerequisites, deliberately untagged.
-/

namespace Flapjack

/-- The clock decrement commutes with adding a constant to a nonzero clock.
This is the arithmetic core of Cake `evaluate_add_clock_eq` for the clocked
evaluator. -/
theorem decPanClock_add (clock ck : Nat) (h : clock ≠ 0) :
    decPanClock (clock + ck) = decPanClock clock + ck := by
  unfold decPanClock
  omega

/-- There is exactly one clock tick from `clock` to `clock - 1`; the result
clock of a nonzero-clock `Tick` run therefore also shifts by `ck`. -/
theorem decPanClock_add_of_pos (clock ck : Nat) (h : 0 < clock) :
    decPanClock (clock + ck) = decPanClock clock + ck :=
  decPanClock_add clock ck (Nat.pos_iff_ne_zero.mp h)

/-- Program-level clock-shift instance for the clock-spending `Tick`
constructor: on a nonzero clock, increasing the input clock by `ck` increases
the returned clock by `ck` with the same `normal` outcome.  This is the
simplest genuinely clock-spending case of the missing whole-program shift
invariant (Cake `evaluate_add_clock_eq`). -/
theorem evalPanValueFfiClockProg_tick_shift
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel ck : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hclock : clock ≠ 0) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + ck) (.tick : Prog α)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
    some (.control (.normal locals globals memory ffi), decPanClock clock + ck) := by
  have hpos : clock + ck ≠ 0 := by omega
  simp only [evalPanValueFfiClockProg, if_neg hpos, Option.pure_def]
  rw [decPanClock_add clock ck hclock]

/-! A zero-condition `While` is independent of the clock.  This is the
    terminating, non-spending branch of Cake's `evaluate_add_clock_eq`; it is
    useful when composing the eventual mutual clock-shift theorem because it
    does not require a body or recursive clock premise. -/
theorem evalPanValueFfiClockProg_while_zero_shift
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
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
    (clock ck : Nat) (condition : Exp α) (body : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word 0)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + ck) (.while condition body)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), clock + ck) := by
  simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition]

/-! A nonzero `While` iteration preserves the clock shift when both the body
    and the resumed loop are supplied at the two clocks.  This is the local
    recursive step needed by Cake's `evaluate_add_clock_eq`; the body and
    resumed-loop witnesses remain explicit until the structural-fuel proof can
    discharge them uniformly. -/
theorem evalPanValueFfiClockProg_while_normal_shift_step
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock ck bodyClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α)) (bodyFfi : FfiState σ)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
    (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : (clock == 0) = false)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (decPanClock clock) body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hbodyShift : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (decPanClock clock + ck) body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock + ck))
    (hrest : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      bodyClock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock))
    (hrestShift : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      (bodyClock + ck) (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock + ck)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      clock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock) ∧
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + ck) (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock + ck) := by
  have hclockNe : clock ≠ 0 := by
    intro hzero
    subst clock
    simp at hclock
  have hclockShift : ((clock + ck) == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro hsum
    apply hclockNe
    omega
  have hdec : decPanClock (clock + ck) = decPanClock clock + ck :=
    decPanClock_add clock ck hclockNe
  constructor
  · simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero, hclock,
      hbody, hrest]
  · simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero, hclockShift,
      hdec, hbodyShift, hrestShift]

/-! A nonzero `While` iteration whose body breaks exits normally at both
    clocks.  Cake's loop-control branch does not recurse, so this terminal
    case needs only the two explicit body evaluator witnesses. -/
theorem evalPanValueFfiClockProg_while_broke_shift_step
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock ck bodyClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α)) (bodyFfi : FfiState σ)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : (clock == 0) = false)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (decPanClock clock) body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.broke bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hbodyShift : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (decPanClock clock + ck) body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.broke bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock + ck)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      clock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock) ∧
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + ck) (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock + ck) := by
  have hclockNe : clock ≠ 0 := by
    intro hzero
    subst clock
    simp at hclock
  have hclockShift : ((clock + ck) == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro hsum
    apply hclockNe
    omega
  have hdec : decPanClock (clock + ck) = decPanClock clock + ck :=
    decPanClock_add clock ck hclockNe
  constructor
  · simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero, hclock,
      hbody]
  · simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero, hclockShift,
      hdec, hbodyShift]

/-! A nonzero `While` iteration whose body continues re-enters the loop at
    both clocks.  The resumed-loop witnesses are explicit, matching Cake's
    `Continue` branch rather than treating it as an unqualified normal body. -/
theorem evalPanValueFfiClockProg_while_continued_shift_step
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock ck bodyClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α)) (bodyFfi : FfiState σ)
    (conditionValue : α) (condition : Exp α) (body : Prog α)
    (outcome : PanValueFfiClockOutcome α σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == (0 : α)) = false)
    (hclock : (clock == 0) = false)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (decPanClock clock) body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.continued bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock))
    (hbodyShift : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (decPanClock clock + ck) body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (.control (.continued bodyLocals bodyGlobals bodyMemory bodyFfi), bodyClock + ck))
    (hrest : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      bodyClock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock))
    (hrestShift : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel bodyLocals bodyGlobals bodyMemory bodyFfi
      (bodyClock + ck) (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock + ck)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      clock (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock) ∧
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (clock + ck) (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
      some (outcome, finalClock + ck) := by
  have hclockNe : clock ≠ 0 := by
    intro hzero
    subst clock
    simp at hclock
  have hclockShift : ((clock + ck) == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro hsum
    apply hclockNe
    omega
  have hdec : decPanClock (clock + ck) = decPanClock clock + ck :=
    decPanClock_add clock ck hclockNe
  constructor
  · simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero, hclock,
      hbody, hrest]
  · simp [evalPanValueFfiClockProg, panValueIteConditionValue, hcondition, hconditionNonzero, hclockShift,
      hdec, hbodyShift, hrestShift]

/-! Cross-clock form of Cake's direct `Call_Ret_Raise` case.  The argument,
    function lookup, parameter binding, payload bound, and callee evaluator
    witnesses remain explicit at both clocks; the caller boundary only clears
    callee locals. -/
theorem evalPanValueFfiClockCall_raised_no_handler_shift_step
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock ck finalClock : Nat)
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
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi
      (decPanClock clock) body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised bodyLocals finalGlobals finalMemory finalFfi exception value),
        finalClock))
    (hbodyShift : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi
      (decPanClock clock + ck) body (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised bodyLocals finalGlobals finalMemory finalFfi exception value),
        finalClock + ck))
    (hwithin : panValuePayloadWithinLimit structs value = true) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value),
        finalClock) ∧
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi (clock + ck)
      none function arguments (memoryAccess := memoryAccess) (contracts := none) =
      some (.control (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception value),
        finalClock + ck) := by
  have hclockShift : clock + ck ≠ 0 := by omega
  have hdec : decPanClock (clock + ck) = decPanClock clock + ck :=
    decPanClock_add clock ck hclock
  constructor
  · simp [evalPanValueFfiClockCall, panValueCallTarget, panValueCallArgumentsValue, hargs, hlookup, hbind, hclock, hbody, hwithin]
  · simp [evalPanValueFfiClockCall, panValueCallTarget, panValueCallArgumentsValue, hargs, hlookup, hbind, hclock, hdec,
      hbodyShift, hwithin]

end Flapjack
