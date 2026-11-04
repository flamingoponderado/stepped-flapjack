import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.TargetSem.MachineSem

/-!
# Step preservation: bounds, composition and machine step counts

Framework for the step-preservation theorem (stepped-flapjack#2). The goal is
an upper bound on the number of machine steps of a particular compiled
program, obtained by

1. proving a step bound for the source program, and
2. composing it with one step-preservation result per compiler pass.

A pass preserves steps with a `LinearBound` `b` when every source run that
finishes within `n` steps has a related target run that finishes within
`b.apply n` steps. The constants of a bound may depend on the program being
compiled (for example, on the size of its largest struct). Bounds compose
through `LinearBound.comp`, so the bound for the whole compiler is the
composition of the per-pass bounds.

At the bottom of the chain, `machineHaltsWithin` counts ticks of the clock of
`evaluateTargetHOL`, the original `targetSem$evaluate`. That clock is
evaluator fuel, not an exact count of machine instructions. One tick is spent
on each executed machine instruction, on each FFI or code-cache entry, and on
observing the halt address. A run that executes `m` instructions and makes `f`
FFI and code-cache calls therefore needs `m + f + 1` ticks. A tick bound is an
upper bound on the executed instructions. A run halts within `n` ticks exactly
when it halts at clock `n` (`machineHaltsWithin_iff_at`). A bounded halt is a
terminating behaviour of the original `machine_sem`
(`machineSemHOL_terminate_of_haltsWithin`).

This is stepped-flapjack infrastructure; nothing here has a HOL counterpart.
-/

namespace SteppedFlapjack.StepPreservation

open Flapjack

/-! ## Linear step bounds -/

/-- A step bound `n ↦ mul * n + add`. -/
structure LinearBound where
  mul : Nat
  add : Nat
  deriving DecidableEq, Repr

namespace LinearBound

/-- The bound applied to a step count. -/
def apply (b : LinearBound) (n : Nat) : Nat := b.mul * n + b.add

/-- The identity bound: a pass that adds no steps. -/
def id : LinearBound := ⟨1, 0⟩

/-- `outer.comp inner` bounds a pass with bound `inner` followed by a pass
with bound `outer`. -/
def comp (outer inner : LinearBound) : LinearBound :=
  ⟨outer.mul * inner.mul, outer.mul * inner.add + outer.add⟩

@[simp] theorem apply_id (n : Nat) : id.apply n = n := by
  simp [apply, id]

theorem apply_comp (outer inner : LinearBound) (n : Nat) :
    (outer.comp inner).apply n = outer.apply (inner.apply n) := by
  simp only [apply, comp, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem apply_mono (b : LinearBound) {n m : Nat} (h : n ≤ m) : b.apply n ≤ b.apply m :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

theorem comp_id (b : LinearBound) : b.comp id = b := by
  cases b; simp [comp, id]

theorem id_comp (b : LinearBound) : id.comp b = b := by
  cases b; simp [comp, id]

theorem comp_assoc (a b c : LinearBound) : (a.comp b).comp c = a.comp (b.comp c) := by
  cases a; cases b; cases c
  simp only [comp, LinearBound.mk.injEq]
  constructor
  · ac_rfl
  · simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

end LinearBound

/-! ## Step-preserving passes -/

/-- A pass preserves steps with bound `b`. For every related source and
target state, a source run that finishes within `n` steps implies a target
run that finishes within `b.apply n` steps. `srcWithin s n` and
`tgtWithin t n` say that the run from `s` (respectively `t`) finishes within
`n` steps. What "finishes" means, and how the two results correspond, is part
of these predicates. -/
def StepPreserving {S T : Type} (srcWithin : S → Nat → Prop) (tgtWithin : T → Nat → Prop)
    (related : S → T → Prop) (b : LinearBound) : Prop :=
  ∀ s t n, related s t → srcWithin s n → tgtWithin t (b.apply n)

/-- Step preservation composes. The bounds compose with `LinearBound.comp`,
and the relations compose through an intermediate state. -/
theorem StepPreserving.trans {S M T : Type} {srcWithin : S → Nat → Prop}
    {midWithin : M → Nat → Prop} {tgtWithin : T → Nat → Prop}
    {r1 : S → M → Prop} {r2 : M → T → Prop} {b1 b2 : LinearBound}
    (h1 : StepPreserving srcWithin midWithin r1 b1)
    (h2 : StepPreserving midWithin tgtWithin r2 b2) :
    StepPreserving srcWithin tgtWithin (fun s t => ∃ m, r1 s m ∧ r2 m t) (b2.comp b1) := by
  rintro s t n ⟨m, hsm, hmt⟩ hs
  rw [LinearBound.apply_comp]
  exact h2 m t _ hmt (h1 s m n hsm hs)

/-- A larger bound is still a bound, provided finishing within some number of
steps is upward closed on the target. -/
theorem StepPreserving.weaken {S T : Type} {srcWithin : S → Nat → Prop}
    {tgtWithin : T → Nat → Prop} {related : S → T → Prop} {b b' : LinearBound}
    (h : StepPreserving srcWithin tgtWithin related b)
    (hmono : ∀ t n m, n ≤ m → tgtWithin t n → tgtWithin t m)
    (hle : ∀ n, b.apply n ≤ b'.apply n) :
    StepPreserving srcWithin tgtWithin related b' := by
  intro s t n hst hs
  exact hmono t _ _ (hle n) (h s t n hst hs)

/-! ## Machine step counts -/

/-- The machine run from `ms` halts with `outcome` and I/O trace `events`
within `n` ticks of the `evaluateTargetHOL` clock. Ticks count executed
machine instructions, FFI and code-cache entries, and the final observation
of the halt address (see the module docstring), so `n` also bounds the
number of executed instructions. -/
def machineHaltsWithin {width : Nat} [NeZero width] {state projection σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state)
    (outcome : HolOutcome) (events : List HolIoEvent) (n : Nat) : Prop :=
  ∃ k ≤ n, ∃ ms' ffi', evaluateTargetHOL mc ffi k ms = (.halt outcome, ms', ffi') ∧
    ffi'.ioEvents = events

theorem machineHaltsWithin_mono {width : Nat} [NeZero width] {state projection σ : Type}
    {mc : MachineConfig width state projection} {ffi : HolFfiState σ} {ms : state}
    {outcome : HolOutcome} {events : List HolIoEvent} {n m : Nat} (hnm : n ≤ m)
    (h : machineHaltsWithin mc ffi ms outcome events n) :
    machineHaltsWithin mc ffi ms outcome events m := by
  obtain ⟨k, hk, rest⟩ := h
  exact ⟨k, Nat.le_trans hk hnm, rest⟩

/-- Halting within `n` ticks is halting at clock `n`. A halted run keeps its
result when the clock grows (`evaluateTargetAddClock`). -/
theorem machineHaltsWithin_iff_at {width : Nat} [NeZero width] {state projection σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state)
    (outcome : HolOutcome) (events : List HolIoEvent) (n : Nat) :
    machineHaltsWithin mc ffi ms outcome events n ↔
      ∃ ms' ffi', evaluateTargetHOL mc ffi n ms = (.halt outcome, ms', ffi') ∧
        ffi'.ioEvents = events := by
  constructor
  · rintro ⟨k, hk, ms', ffi', hrun, hev⟩
    refine ⟨ms', ffi', ?_, hev⟩
    have := evaluateTargetAddClock mc ffi k ms (n - k) _ ms' ffi' hrun (by simp)
    rwa [Nat.add_sub_cancel' hk] at this
  · rintro ⟨ms', ffi', hrun, hev⟩
    exact ⟨n, Nat.le_refl n, ms', ffi', hrun, hev⟩

/-- A bounded halt is a terminating behaviour of the original `machine_sem`. -/
theorem machineSemHOL_terminate_of_haltsWithin {width : Nat} [NeZero width]
    {state projection σ : Type} {mc : MachineConfig width state projection}
    {ffi : HolFfiState σ} {ms : state} {outcome : HolOutcome} {events : List HolIoEvent}
    {n : Nat} (h : machineHaltsWithin mc ffi ms outcome events n) :
    machineSemHOL mc ffi ms (.terminate outcome events) := by
  obtain ⟨k, -, ms', ffi', hrun, hev⟩ := h
  exact ⟨k, ms', ffi', hrun, hev⟩

end SteppedFlapjack.StepPreservation
