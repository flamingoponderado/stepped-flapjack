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

theorem mem_code (op : HolMemop) (r a : Nat) (w : BitVec width)
    (s t : StackSemStateFiniteExact width C F)
    (h : StackSemIntegerInstructions.instInteger (.mem op r (.addr a w)) s = some (some t)) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  cases op
  case load =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hm : memLoad av s with
      | none => simp [ha, hm] at h
      | some wv =>
        simp [ha, hm] at h
        subst t
        exact setVar_code _ _ _
  case load8 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hm : memLoadByteAuxExact s.memory s.mdomain s.be av with
      | none => simp [ha, hm] at h
      | some wv =>
        simp [ha, hm] at h
        subst t
        exact setVar_code _ _ _
  case load16 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    simp at h
  case load32 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hm : memLoad32Exact s.memory s.mdomain s.be av with
      | none => simp [ha, hm] at h
      | some wv =>
        simp [ha, hm] at h
        subst t
        exact setVar_code _ _ _
  case store =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hr : getVar r s with
      | none => simp [ha, hr] at h
      | some wv =>
        cases hm : memStore av wv s with
        | none => simp [ha, hr, hm] at h
        | some s1 =>
          simp [ha, hr, hm] at h
          subst t
          exact memStore_code _ _ _ _ hm
  case store8 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hr : getVar r s with
      | none => simp [ha, hr] at h
      | some wv =>
        cases wv with
        | word ww =>
          cases hm : memStoreByteAuxExact s.memory s.mdomain s.be av (ww.setWidth 8) with
          | none => simp [ha, hr, hm] at h
          | some newM =>
            simp [ha, hr, hm] at h
            subst t
            exact ⟨rfl, rfl⟩
        | loc l => simp [ha, hr] at h
  case store16 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    simp at h
  case store32 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hr : getVar r s with
      | none => simp [ha, hr] at h
      | some wv =>
        cases wv with
        | word ww =>
          cases hm : memStore32Exact s.memory s.mdomain s.be av (ww.setWidth 32) with
          | none => simp [ha, hr, hm] at h
          | some newM =>
            simp [ha, hr, hm] at h
            subst t
            exact ⟨rfl, rfl⟩
        | loc l => simp [ha, hr] at h
theorem instHOL_code (i : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : StackSemInst.instHOL i s = some t) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  cases i
  case skip =>
    simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at h ⊢
    rw [← h]; exact ⟨rfl, rfl⟩
  case const dest w =>
    simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at h
    exact assign_code _ _ _ _ h
  case arith operation =>
    cases operation <;> simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at h ⊢
    all_goals try (split_ifs at h)
    all_goals try (split at h)
    all_goals try (simp at h)
    all_goals try (exact assign_code _ _ _ _ h)
    all_goals try (obtain ⟨-, h⟩ := h)
    all_goals try (exact setVar_code _ _ _)
    all_goals try (rw [← h]; exact ⟨rfl, rfl⟩)
  case mem op dest addr =>
    simp only [StackSemInst.instHOL] at h
    cases addr with
    | addr a w =>
      cases hi : StackSemIntegerInstructions.instInteger (.mem op dest (.addr a w)) s with
      | none => simp [hi] at h
      | some o =>
        cases o with
        | none => simp [hi] at h
        | some t' =>
          simp [hi] at h
          subst t
          exact mem_code op dest a w s t' hi
  case fp op =>
    cases op <;> simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
      StackSemFpRegisterInstructions.instFpRegister,
      StackSemFpRegisterInstructions.instFpSqrt] at h ⊢
    all_goals try (split_ifs at h)
    all_goals try (split at h)
    all_goals try (simp at h)
    all_goals try (rw [← h]; exact ⟨rfl, rfl⟩)
    all_goals try (exact fpToInt_code _ _ _ _ h)
    all_goals try (exact fpFromInt_code _ _ _ _ h)
theorem sptAListLookup_mem {α : Type} (key : Nat) (entries : List (Nat × α)) (value : α)
    (h : sptAListLookup key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [sptAListLookup] at h
  | cons entry entries ih =>
    obtain ⟨other, value'⟩ := entry
    by_cases hk : key = other
    · subst hk
      simp [sptAListLookup] at h
      simp [h]
    · simp [sptAListLookup, hk] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem install_codeBound {B K : Nat} {bounds : BitVec width × BitVec width}
    (s : StackSemStateFiniteExact width C F)
    (progs : List (Nat × HolProg width))
    (hcode : codeBound B bounds K s)
    (horacle : ∀ name prog, (name, prog) ∈ progs → leafCost B bounds prog ≤ K)
    (label : Nat) (program : HolProg width)
    (h : sptLookup label (sptUnion s.code (sptFromAList progs)) = some program) :
    leafCost B bounds program ≤ K := by
  rw [sptLookup_sptUnion] at h
  cases hl : sptLookup label s.code with
  | some v =>
    simp only [hl] at h
    simp only [Option.some.injEq] at h
    exact hcode label program (h ▸ hl)
  | none =>
    simp only [hl] at h
    rw [sptLookup_sptFromAList] at h
    exact horacle label program (sptAListLookup_mem label progs program h)
theorem install_oracleBound {B K : Nat} {bounds : BitVec width × BitVec width}
    (s : StackSemStateFiniteExact width C F)
    (h : oracleBound B bounds K s)
    (index name : Nat) (program : HolProg width)
    (hmem : (name, program) ∈ ((holShiftSeq 1 s.compileOracle) index).2.1) :
    leafCost B bounds program ≤ K := by
  simp only [holShiftSeq] at hmem
  exact h (index + 1) name program hmem
theorem storeConstSem_code {resultWidth : Nat} [NeZero resultWidth]
    (t1 t2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (h : (StackSemStoreConsts.storeConstSem (resultWidth := resultWidth) t1 t2 s).2 = t) :
    t.code = s.code ∧ t.compileOracle = s.compileOracle := by
  rw [← h]
  by_cases hnodup : ¬ [0, 1, 2, 3, t1, t2].Nodup
  · simp [StackSemStoreConsts.storeConstSem, if_pos hnodup]
  · simp only [StackSemStoreConsts.storeConstSem, if_neg hnodup]
    cases h1 : getVar 1 s with
    | none => simp
    | some v1 =>
      cases h2 : getVar 2 s with
      | none => simp
      | some v2 =>
        cases h3 : getVar 3 s with
        | none => simp
        | some v3 =>
          cases v1 with
          | word i =>
            cases v2 with
            | word a =>
              cases v3 with
              | word off =>
                cases hc : StackSemStoreConsts.copyWordsExact i.toNat a off s.bitmaps (fun x => s.mdomain x = true) s.memory with
                | none => simp [hc]
                | some p =>
                  obtain ⟨a', m⟩ := p
                  simp [hc]
                  split <;> exact ⟨rfl, rfl⟩
              | loc l => simp
            | loc l => simp
          | loc l => simp
end SteppedFlapjack.StackRemoveSteps.CompCorrect
