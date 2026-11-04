import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Statement

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Guarded.lean`
(stepped-flapjack#2, phase C1): the cases that cannot occur under `state_rel`,
for `FlattenPropWithin`. The statements and proofs follow the original. -/

/-! `flatten_correct` cases whose StackSem clause fails under `state_rel`:
`state_rel` forces `¬use_alloc`, `¬use_store` and `¬use_stack`, so `Alloc`,
`StoreConsts`, `Get`, `Set`, `OpCurrHeap`, the stack-frame instructions,
`BitmapLoad` and `DataBufferWrite` all return `SOME Error`, contradicting the
hypothesis `r ≠ SOME Error` (as in the HOL proof, by `state_rel_def`). -/

namespace SteppedFlapjack.StackToLabSteps
open Flapjack hiding flattenHOL
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
  (FlattenHyps FlattenConcl MeasureLt appListAppendList appListAppendAppend)
open SteppedFlapjack.StackSteps

section
variable {width : Nat} [NeZero width] {C F : Type}

theorem relNoStack {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    s.useStack = false ∧ s.useStore = false ∧ s.useAlloc = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    us, ust, ua, _⟩ := rel
  simp_all

/-- Shared shape: the clause returns `SOME Error` from the state relation. -/
private theorem guarded {prog : HolProg width} {s1 : StackSemStateFiniteExact width C F}
    (h : ∀ (t : Flapjack.Compiler.Backend.LabSem.State width C F), stateRel s1 t →
      (StackSemEvaluate.evaluate (prog, s1)).1 = some .error) :
    FlattenPropWithin prog s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -⟩
  have := h t1 rel
  rw [ev] at this
  exact absurd this nerr

theorem flattenCorrectAlloc (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    FlattenPropWithin (.alloc k : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_alloc]; simp [(relNoStack rel).2.2]

theorem flattenCorrectStoreConsts (s1 : StackSemStateFiniteExact width C F)
    (a b : Nat) (stub : Option Nat) :
    FlattenPropWithin (.storeConsts a b stub : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_storeConsts]; simp [(relNoStack rel).2.1]

theorem flattenCorrectGet (s1 : StackSemStateFiniteExact width C F) (v : Nat)
    (name : StoreName) : FlattenPropWithin (.get v name : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_get]; simp [(relNoStack rel).2.1]

theorem flattenCorrectSet (s1 : StackSemStateFiniteExact width C F) (v : Nat)
    (name : StoreName) : FlattenPropWithin (.set name v : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_set]; simp [(relNoStack rel).2.1]

theorem flattenCorrectOpCurrHeap (s1 : StackSemStateFiniteExact width C F)
    (op : Compiler.Encoders.Asm.HolBinop) (v src : Nat) :
    FlattenPropWithin (.opCurrHeap op v src : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_opCurrHeap]; simp [(relNoStack rel).2.1]

theorem flattenCorrectStackAlloc (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    FlattenPropWithin (.stackAlloc k : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackAlloc]; simp [(relNoStack rel).1]

theorem flattenCorrectStackFree (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    FlattenPropWithin (.stackFree k : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackFree]; simp [(relNoStack rel).1]

theorem flattenCorrectStackLoad (s1 : StackSemStateFiniteExact width C F) (r k : Nat) :
    FlattenPropWithin (.stackLoad r k : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackLoad]; simp [(relNoStack rel).1]

theorem flattenCorrectStackLoadAny (s1 : StackSemStateFiniteExact width C F) (r rn : Nat) :
    FlattenPropWithin (.stackLoadAny r rn : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackLoadAny]; simp [(relNoStack rel).1]

theorem flattenCorrectStackStore (s1 : StackSemStateFiniteExact width C F) (r k : Nat) :
    FlattenPropWithin (.stackStore r k : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackStore]; simp [(relNoStack rel).1]

theorem flattenCorrectStackStoreAny (s1 : StackSemStateFiniteExact width C F) (r rn : Nat) :
    FlattenPropWithin (.stackStoreAny r rn : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackStoreAny]; simp [(relNoStack rel).1]

theorem flattenCorrectStackGetSize (s1 : StackSemStateFiniteExact width C F) (r : Nat) :
    FlattenPropWithin (.stackGetSize r : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackGetSize]; simp [(relNoStack rel).1]

theorem flattenCorrectStackSetSize (s1 : StackSemStateFiniteExact width C F) (r : Nat) :
    FlattenPropWithin (.stackSetSize r : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackSetSize]; simp [(relNoStack rel).1]

theorem flattenCorrectBitmapLoad (s1 : StackSemStateFiniteExact width C F) (r v : Nat) :
    FlattenPropWithin (.bitmapLoad r v : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_bitmapLoad]; simp [(relNoStack rel).1]

theorem flattenCorrectDataBufferWrite (s1 : StackSemStateFiniteExact width C F) (r1 r2 : Nat) :
    FlattenPropWithin (.dataBufferWrite r1 r2 : HolProg width) s1 :=
  guarded fun t rel => by
    rw [StackSemEvaluate.evaluate_dataBufferWrite]; simp [(relNoStack rel).1]

end

end SteppedFlapjack.StackToLabSteps
