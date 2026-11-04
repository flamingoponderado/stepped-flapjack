import SteppedFlapjack.StackToLabSteps

/-! Compile-time checks of the bounded `stack_to_lab` simulation. -/

namespace SteppedFlapjack.Test.StackToLabSteps

open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect (FlattenHyps FlattenConcl)
open SteppedFlapjack.StackSteps SteppedFlapjack.StackToLabSteps

-- Three LabSem instructions per StackSem step: a returning call with an
-- exception handler runs `LocValue`, the jump to the callee and the jump over
-- the handler.
example : flattenStepFactor = 3 := rfl

-- A leaf, such as `Skip`, is allowed `flattenStepFactor` ticks.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    flattenStepFactor * steps ((.skip : HolProg 64), s) = 3 := by
  rw [stepFactorLeaf rfl]; rfl

-- The bounded conclusion forgets to Flapjack's `flatten_correct` conclusion.
example {width : Nat} [NeZero width] {C F : Type} (prog : HolProg width)
    (s1 : StackSemStateFiniteExact width C F) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : State width C F) (h : FlattenHyps prog s1 t r s2 n l cs bs t1) :
    FlattenConcl prog t r s2 n l cs bs t1 :=
  flattenCorrect_of_within prog s1 t r s2 n l cs bs t1 h

-- The bounded simulation from Flapjack's hypotheses.
example {width : Nat} [NeZero width] {C F : Type} (prog : HolProg width)
    (s1 : StackSemStateFiniteExact width C F) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : State width C F) (h : FlattenHyps prog s1 t r s2 n l cs bs t1) :
    FlattenConclWithin prog s1 t r s2 n l cs bs t1 :=
  flattenPropAll prog s1 t r s2 n l cs bs t1 h

-- Removing unused clock from a LabSem run.
example {width : Nat} [NeZero width] {C F : Type} (t : State width C F) (c d : Nat)
    (res : MachineResult) (t2 : State width C F)
    (h : evaluate { t with clock := c + d } = (res, t2)) (hd : d < t2.clock) :
    evaluate { t with clock := c } = (res, { t2 with clock := t2.clock - d }) :=
  evaluate_subClock t c d res t2 h hd

-- The shape of the semantics-level bound: an entry run completing with
-- outcome `o` within `n` steps is matched by a LabSem run from clock at most
-- `3 * (n + h)`, with `h` bounding the halting procedure's steps.
example {width : Nat} [NeZero width] {C F : Type} {start k n h : Nat}
    {s1 : StackSemStateFiniteExact width C F} {s2 : State width C F}
    {res : Option (StackSemResult width)} {s' : StackSemStateFiniteExact width C F}
    {o : HolOutcome}
    (halt : haltAssum C F s1.code) (rel : stateRel s1 s2)
    (hpc : locToPc start 0 s2.code = some s2.pc)
    (hhalt : res = some (.result (.loc 1 0)) → haltStepsWithin C F s1.code h)
    (ev : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s1 with clock := k }) = (res, s'))
    (hn : steps ((.call none (.inl start) none : HolProg width), { s1 with clock := k }) ≤ n)
    (hres : stackEntryClass res = .CompleteResult o) :
    ∃ m ≤ 3 * (n + h), ∃ t',
      evaluate { s2 with clock := m } = (.halt o, t') ∧ t'.ffi.ioEvents = s'.ffi.ioEvents :=
  flattenSemanticsWithin halt rel hpc hhalt ev hn hres

-- A run ending in `Halt` needs no step bound for procedure 1: take `h = 0`.
example {width : Nat} [NeZero width] {C F : Type} {start k n : Nat}
    {s1 : StackSemStateFiniteExact width C F} {s2 : State width C F}
    {w : BitVec width} {s' : StackSemStateFiniteExact width C F}
    (halt : haltAssum C F s1.code) (rel : stateRel s1 s2)
    (hpc : locToPc start 0 s2.code = some s2.pc)
    (ev : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s1 with clock := k }) = (some (.halt (.word w)), s'))
    (hn : steps ((.call none (.inl start) none : HolProg width), { s1 with clock := k }) ≤ n) :
    ∃ m ≤ 3 * n, ∃ t',
      evaluate { s2 with clock := m } =
        (.halt (if w = 0 then .success else .resourceLimitHit), t') ∧
      t'.ffi.ioEvents = s'.ffi.ioEvents := by
  have := flattenSemanticsWithin (h := 0) halt rel hpc (by simp) ev hn
    (o := if w = 0 then .success else .resourceLimitHit) (by simp [stackEntryClass])
  simpa [flattenStepFactor] using this

end SteppedFlapjack.Test.StackToLabSteps
