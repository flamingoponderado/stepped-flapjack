import SteppedFlapjack.StackRemoveSteps.CompCorrect.LeafStepsAll
import Flapjack.Misc.Sptree

/-! Code and compile-oracle bounds, and their preservation by `evaluate`
(stepped-flapjack#2, phase C3).

The step-counted correctness theorem needs a single program-dependent factor `K`
that bounds the leaf cost of every program the evaluator can jump to. Programs
come from two places: the code already in the state, and the code the
`install` instruction adds from the compile oracle. `install` is the only
constructor that changes `code` or `compileOracle`, so both bounds must be
carried through the evaluation. This file states them and proves that
`evaluate` preserves them.

`codeBound s` bounds `leafCost` of every program reachable through `s.code`;
`oracleBound s` bounds every program the oracle can hand to `install`. For a
concrete Pancake source both are finite, calculable facts, discharged when the
theorem is instantiated. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.Asm

variable {width : Nat} [NeZero width] {C F : Type}

/-- Every program reachable through the state's code has leaf cost at most `K`. -/
def codeBound (B : Nat) (bounds : BitVec width × BitVec width) (K : Nat)
    (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (label : Nat) (program : HolProg width),
    sptLookup label s.code = some program → leafCost B bounds program ≤ K

/-- Every program the compile oracle can hand to `install` has leaf cost at most
`K`. -/
def oracleBound (B : Nat) (bounds : BitVec width × BitVec width) (K : Nat)
    (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (index name : Nat) (program : HolProg width),
    (name, program) ∈ (s.compileOracle index).2.1 → leafCost B bounds program ≤ K

/-- The garbage collector rebuilds `stack`, `store`, `regs` and `memory` and
leaves `code` and `compileOracle` untouched. -/
theorem gc_code (s t : StackSemStateFiniteExact width C F)
    (h : StackSemAllocation.gc s = some t) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemAllocation.gc] at h
  split at h
  · simp_all
  · rcases he : StackSem.encStack s.bitmaps (List.drop s.stackSpace s.stack) with _ | roots
    · simp [he] at h
    · rcases hg : s.gcFun (roots, s.memory, s.mdomain, s.store) with _ | ⟨r', mem, st⟩
      · simp [he, hg] at h
      · rcases hd : StackSem.decStack s.bitmaps r' (List.drop s.stackSpace s.stack) with _ | stack'
        · simp [he, hg, hd] at h
        · simp [he, hg, hd] at h
          subst t
          simp

/-- `alloc` keeps `code` and `compileOracle`. -/
theorem alloc_code (v : BitVec width) (s : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemAllocation.alloc v s = (result, post)) :
    post.code = s.code ∧ post.compileOracle = s.compileOracle := by
  simp only [StackSemAllocation.alloc] at run
  rcases hc : StackSemAllocation.gc (setStore .allocSize (.word v) s) with _ | collected
  · simp [hc] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨rfl, rfl⟩
  · have hg := gc_code _ _ hc
    simp only [StackSemStateOps.setStore] at hg
    rcases hs : collected.store.lookup .allocSize with _ | amount
    · simp [hc, hs] at run
      obtain ⟨-, rfl⟩ := run
      exact hg
    · rcases hsp : StackSemAllocation.hasSpace amount collected.store with _ | sp
      · simp [hc, hs, hsp] at run
        obtain ⟨-, rfl⟩ := run
        exact hg
      · cases sp
        · simp [hc, hs, hsp] at run
          obtain ⟨-, rfl⟩ := run
          exact hg
        · simp [hc, hs, hsp] at run
          obtain ⟨-, rfl⟩ := run
          exact hg

/-- Register writes keep `code` and `compileOracle`. -/
theorem setVar_code (v : Nat) (x : WordLocW width) (s : StackSemStateFiniteExact width C F) :
    (setVar v x s).code = s.code ∧ (setVar v x s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- Store writes keep `code` and `compileOracle`. -/
theorem setStore_code (v : WordStoreHOL) (x : WordLocW width)
    (s : StackSemStateFiniteExact width C F) :
    (setStore v x s).code = s.code ∧ (setStore v x s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- FP register writes keep `code` and `compileOracle`. -/
theorem setFpVar_code (v : Nat) (x : BitVec 64) (s : StackSemStateFiniteExact width C F) :
    (setFpVar v x s).code = s.code ∧ (setFpVar v x s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- `emptyEnv` keeps `code` and `compileOracle`. -/
theorem emptyEnv_code (s : StackSemStateFiniteExact width C F) :
    (emptyEnv s).code = s.code ∧ (emptyEnv s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- `decClock` keeps `code` and `compileOracle`. -/
theorem decClock_code (s : StackSemStateFiniteExact width C F) :
    (decClock s).code = s.code ∧ (decClock s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- Memory writes keep `code` and `compileOracle`. -/
theorem memStore_code (a : BitVec width) (w : WordLocW width)
    (s t : StackSemStateFiniteExact width C F) (h : memStore a w s = some t) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemStateOps.memStore] at h
  split at h
  · obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  · simp at h

/-- Expression assignment keeps `code` and `compileOracle`. -/
theorem assign_code (reg : Nat) (exp : WordLangExpHOL (BitVec width))
    (s t : StackSemStateFiniteExact width C F)
    (h : StackSemExpressions.assign reg exp s = some t) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemExpressions.assign] at h
  split at h
  · simp at h
  · obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- Int-to-FP conversions keep `code` and `compileOracle`. -/
theorem fpToInt_code (d1 d2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (h : StackSemFpRegisterInstructions.instFpToInt d1 d2 s = some t) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemFpRegisterInstructions.instFpToInt] at h
  cases hg : getFpVar d2 s with
  | none => simp [hg] at h
  | some f =>
    cases hi : holFp64ToInt .roundTiesToEven f with
    | none => simp [hg, hi] at h
    | some i =>
      simp only [hg, hi] at h
      split_ifs at h
      all_goals try (obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      all_goals try (cases hf : getFpVar (d1 / 2) s)
      all_goals try (simp [hf] at h)
      all_goals try (obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩)

/-- FP-to-int conversions keep `code` and `compileOracle`. -/
theorem fpFromInt_code (d1 d2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (h : StackSemFpRegisterInstructions.instFpFromInt d1 d2 s = some t) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemFpRegisterInstructions.instFpFromInt] at h
  split_ifs at h
  all_goals try (cases hg : getFpVar d2 s)
  all_goals try (cases hk : getFpVar (d2 / 2) s)
  all_goals try (simp [hg] at h)
  all_goals try (simp [hk] at h)
  all_goals try (obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩)

end SteppedFlapjack.StackRemoveSteps.CompCorrect
