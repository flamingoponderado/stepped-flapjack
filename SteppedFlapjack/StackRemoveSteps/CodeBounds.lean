import SteppedFlapjack.StackRemoveSteps.CompCorrect.LeafStepsAll
import Flapjack.Misc.Sptree
import Flapjack.Pancake.Semantics.LoopSemStateExact.ShMem

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
`oracleBound s` bounds every program the oracle can hand to `install`. This is
a uniform assumption on the entire oracle: a concrete source program alone
does not imply it, since the oracle may supply programs of unbounded cost. A
use site must establish it or use a run-specific bound. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.StackSemMeasure
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
theorem shMemLoad_code (v : Nat) (addr : BitVec width) (nb : Nat)
    (s : LoopSemStateFiniteExact width F) :
    (LoopSemStateFiniteExact.shMemLoad v addr nb s).2.code = s.code := by
  simp only [LoopSemStateFiniteExact.shMemLoad]
  by_cases hnb : nb = 0
  · simp only [if_pos hnb]
    split_ifs with hd
    · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb] (panWordToBytesHOL addr false) with
      | final outcome => simp [LoopSemStateFiniteExact.callEnv]
      | ret newFfi newBytes => simp [LoopSemStateFiniteExact.setVar]
    · rfl
  · simp only [if_neg hnb]
    split_ifs with hd
    · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb] (panWordToBytesHOL addr false) with
      | final outcome => simp [LoopSemStateFiniteExact.callEnv]
      | ret newFfi newBytes => simp [LoopSemStateFiniteExact.setVar]
    · rfl

theorem shMemStore_code (v : Nat) (addr : BitVec width) (nb : Nat)
    (s : LoopSemStateFiniteExact width F) :
    (LoopSemStateFiniteExact.shMemStore v addr nb s).2.code = s.code := by
  simp only [LoopSemStateFiniteExact.shMemStore]
  cases hs : sptLookup v s.locals with
  | none => simp
  | some val =>
    cases val with
    | word w =>
      by_cases hnb : nb = 0
      · simp only [if_pos hnb]
        split_ifs with hd
        · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb] (panWordToBytesHOL w false ++ panWordToBytesHOL addr false) with
          | final outcome => simp [LoopSemStateFiniteExact.callEnv]
          | ret newFfi _ => simp
        · rfl
      · simp only [if_neg hnb]
        split_ifs with hd
        · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb] ((panWordToBytesHOL w false).take nb ++ panWordToBytesHOL addr false) with
          | final outcome => simp [LoopSemStateFiniteExact.callEnv]
          | ret newFfi _ => simp
        · rfl
    | loc l => simp

theorem shMemOp_code (op : WordMemOp) (r : Nat) (ad : BitVec width)
    (s t : LoopSemStateFiniteExact width F)
    (h : (LoopSemStateFiniteExact.shMemOp op r ad s).2 = t) :
    t.code = s.code := by
  rw [← h]
  cases op <;> simp [LoopSemStateFiniteExact.shMemOp, shMemLoad_code, shMemStore_code]
theorem codeBound_congr {B K : Nat} {bounds : BitVec width × BitVec width}
    {s t : StackSemStateFiniteExact width C F}
    (hc : t.code = s.code) (h : codeBound B bounds K s) : codeBound B bounds K t := by
  intro label program hl
  exact h label program (by rw [← hc]; exact hl)

theorem oracleBound_congr {B K : Nat} {bounds : BitVec width × BitVec width}
    {s t : StackSemStateFiniteExact width C F}
    (ho : t.compileOracle = s.compileOracle) (h : oracleBound B bounds K s) :
    oracleBound B bounds K t := by
  intro index name program hl
  exact h index name program (by rw [← ho]; exact hl)
theorem stackShMemLoad_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad r address s).2.code = s.code := by
  simp only [StackSemShMem.shMemLoad]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [0] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp

theorem stackShMemLoadByte_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoadByte r address s).2.code = s.code := by
  simp only [StackSemShMem.shMemLoadByte]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [1] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp

theorem stackShMemLoad16_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad16 r address s).2.code = s.code := by
  simp only [StackSemShMem.shMemLoad16]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [2] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp

theorem stackShMemLoad32_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad32 r address s).2.code = s.code := by
  simp only [StackSemShMem.shMemLoad32]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [4] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp

theorem stackShMemStore_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore r address s).2.code = s.code := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [0] (panWordToBytesHOL w false ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore, hv]

theorem stackShMemStoreByte_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStoreByte r address s).2.code = s.code := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStoreByte, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStoreByte, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [1] ([getByteHOL8 0 w false] ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStoreByte, hv]

theorem stackShMemStore16_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore16 r address s).2.code = s.code := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore16, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore16, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [2] ((panWordToBytesHOL w false).take 2 ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore16, hv]

theorem stackShMemStore32_code (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore32 r address s).2.code = s.code := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore32, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore32, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [4] ((panWordToBytesHOL w false).take 4 ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore32, hv]

theorem stackShMemOp_code (op : WordMemOp) (r : Nat) (address : BitVec width)
    (s t : StackSemStateFiniteExact width C F)
    (h : (StackSemShMem.shMemOp op r address s).2 = t) : t.code = s.code := by
  rw [← h]
  cases op
  case load => exact stackShMemLoad_code r address s
  case load8 => exact stackShMemLoadByte_code r address s
  case load16 => exact stackShMemLoad16_code r address s
  case load32 => exact stackShMemLoad32_code r address s
  case store => exact stackShMemStore_code r address s
  case store8 => exact stackShMemStoreByte_code r address s
  case store16 => exact stackShMemStore16_code r address s
  case store32 => exact stackShMemStore32_code r address s
theorem stackShMemLoad_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad r address s).2.compileOracle = s.compileOracle := by
  simp only [StackSemShMem.shMemLoad]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [0] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemLoadByte_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoadByte r address s).2.compileOracle = s.compileOracle := by
  simp only [StackSemShMem.shMemLoadByte]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [1] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemLoad16_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad16 r address s).2.compileOracle = s.compileOracle := by
  simp only [StackSemShMem.shMemLoad16]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [2] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemLoad32_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad32 r address s).2.compileOracle = s.compileOracle := by
  simp only [StackSemShMem.shMemLoad32]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [4] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemStore_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore r address s).2.compileOracle = s.compileOracle := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [0] (panWordToBytesHOL w false ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore, hv]
theorem stackShMemStoreByte_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStoreByte r address s).2.compileOracle = s.compileOracle := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStoreByte, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStoreByte, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [1] ([getByteHOL8 0 w false] ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStoreByte, hv]
theorem stackShMemStore16_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore16 r address s).2.compileOracle = s.compileOracle := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore16, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore16, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [2] ((panWordToBytesHOL w false).take 2 ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore16, hv]
theorem stackShMemStore32_oracle (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore32 r address s).2.compileOracle = s.compileOracle := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore32, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore32, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [4] ((panWordToBytesHOL w false).take 4 ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore32, hv]
theorem stackShMemOp_oracle (op : WordMemOp) (r : Nat) (address : BitVec width)
    (s t : StackSemStateFiniteExact width C F)
    (h : (StackSemShMem.shMemOp op r address s).2 = t) : t.compileOracle = s.compileOracle := by
  rw [← h]
  cases op
  case load => exact stackShMemLoad_oracle r address s
  case load8 => exact stackShMemLoadByte_oracle r address s
  case load16 => exact stackShMemLoad16_oracle r address s
  case load32 => exact stackShMemLoad32_oracle r address s
  case store => exact stackShMemStore_oracle r address s
  case store8 => exact stackShMemStoreByte_oracle r address s
  case store16 => exact stackShMemStore16_oracle r address s
  case store32 => exact stackShMemStore32_oracle r address s

/-- Transfer both bounds from a state to another with the same code map and
compile oracle. -/
theorem codeBounds_transfer {B K : Nat} {bounds : BitVec width × BitVec width}
    {s t : StackSemStateFiniteExact width C F}
    (hc : t.code = s.code) (ho : t.compileOracle = s.compileOracle)
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t :=
  ⟨codeBound_congr hc hcode, oracleBound_congr ho horacle⟩

theorem codeBounds_skip {B K : Nat} {bounds : BitVec width × BitVec width}
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.skip : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_skip] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨hcode, horacle⟩

theorem codeBounds_break {B K : Nat} {bounds : BitVec width × BitVec width}
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.break n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_break] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨hcode, horacle⟩

theorem codeBounds_continue {B K : Nat} {bounds : BitVec width × BitVec width}
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.continue n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_continue] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨hcode, horacle⟩

theorem codeBounds_halt {B K : Nat} {bounds : BitVec width × BitVec width}
    (v : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.halt v : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hv : getVar v s with
  | none => rw [evaluate_halt, hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some w =>
    rw [evaluate_halt, hv] at h; obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle

theorem codeBounds_tick {B K : Nat} {bounds : BitVec width × BitVec width}
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.tick : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_tick] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (decClock_code s).1 (decClock_code s).2 hcode horacle
theorem codeBounds_ret {B K : Nat} {bounds : BitVec width × BitVec width}
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.ret n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hv : getVar n s with
  | none => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some w =>
    cases w with
    | loc l1 l2 => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | word w => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩

theorem codeBounds_raise {B K : Nat} {bounds : BitVec width × BitVec width}
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.raise n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hv : getVar n s with
  | none => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some w =>
    cases w with
    | loc l1 l2 => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | word w => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩

theorem codeBounds_locValue {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 l1 l2 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.locValue r0 l1 l2 : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_locValue] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩

theorem codeBounds_inst {B K : Nat} {bounds : BitVec width × BitVec width}
    (i : HolInst width) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.inst i : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rcases hi : StackSemInst.instHOL i s with _ | ss
  · rw [evaluate_inst, hi] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · rw [evaluate_inst, hi] at h; obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (instHOL_code i s _ hi).1 (instHOL_code i s _ hi).2 hcode horacle

theorem codeBounds_get {B K : Nat} {bounds : BitVec width × BitVec width}
    (v : Nat) (name : StoreName) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.get v name : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hs : s.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) with
  | none =>
    rw [evaluate_get, hs] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩)
  | some x =>
    rw [evaluate_get, hs] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle
    · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩

theorem codeBounds_set {B K : Nat} {bounds : BitVec width × BitVec width}
    (name : StoreName) (v : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.set name v : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hv : getVar v s with
  | none =>
    rw [evaluate_set, hv] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩)
  | some w =>
    rw [evaluate_set, hv] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer (setStore_code _ _ _).1 (setStore_code _ _ _).2 hcode horacle
    · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩

theorem codeBounds_opCurrHeap {B K : Nat} {bounds : BitVec width × BitVec width}
    (binop : HolBinop) (v src : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.opCurrHeap binop v src : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hw : StackSemExpressions.wordExp s (.op binop [.var src, .lookup .currHeap]) with
  | none =>
    rw [evaluate_opCurrHeap, hw] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩)
  | some w =>
    rw [evaluate_opCurrHeap, hw] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle
    · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
theorem codeBounds_stackAlloc {B K : Nat} {bounds : BitVec width × BitVec width}
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackAlloc n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_stackAlloc] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer rfl rfl hcode horacle

theorem codeBounds_stackFree {B K : Nat} {bounds : BitVec width × BitVec width}
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackFree n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_stackFree] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer rfl rfl hcode horacle

theorem codeBounds_stackLoad {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackLoad r0 n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_stackLoad] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle

theorem codeBounds_stackGetSize {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackGetSize r0 : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_stackGetSize] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle

theorem codeBounds_bitmapLoad {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 v : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.bitmapLoad r0 v : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_bitmapLoad] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · cases hv : getVar v s with
    | none => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | some w =>
      cases w
      case loc l1 l2 => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      case word wd =>
        simp only [hv] at h
        split_ifs at h with hc
        · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
        · obtain ⟨-, rfl⟩ := h
          exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle
theorem codeBounds_stackStore {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackStore r0 n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_stackStore] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
  · cases hv : getVar r0 s
    case none =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
    case some val =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer rfl rfl hcode horacle

theorem codeBounds_stackSetSize {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackSetSize r0 : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_stackSetSize] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  · cases hv : getVar r0 s
    case none =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    case some val =>
      cases val
      case loc l1 l2 => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      case word wd =>
        simp only [hv] at h
        split_ifs at h with hc
        · obtain ⟨-, rfl⟩ := h
          exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
        · obtain ⟨-, rfl⟩ := h
          exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle
theorem codeBounds_seq {B K : Nat} {bounds : BitVec width × BitVec width}
    (a b : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.seq a b : HolProg width), s) = (r, t))
    (ihA : ∀ (r : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F),
      evaluate (a, s) = (r, post) → codeBound B bounds K s → oracleBound B bounds K s →
      codeBound B bounds K post ∧ oracleBound B bounds K post)
    (ihB : ∀ (middle : StackSemStateFiniteExact width C F),
      evaluate (a, s) = (none, middle) →
      ∀ (r : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F),
      evaluate (b, middle) = (r, post) → codeBound B bounds K middle → oracleBound B bounds K middle →
      codeBound B bounds K post ∧ oracleBound B bounds K post)
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rcases hfxA : evaluate (a, s) with ⟨ra, s1⟩
  have hA := ihA ra s1 hfxA hcode horacle
  cases ra with
  | none =>
    have hrunB : evaluate (b, s1) = (r, t) := by
      have h' := h
      rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, hfxA] at h'
      dsimp only at h'
      exact h'
    exact ihB s1 hfxA r t hrunB hA.1 hA.2
  | some rr =>
    have h' := h
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, hfxA] at h'
    dsimp only at h'
    obtain ⟨-, rfl⟩ := h'
    exact hA
theorem codeBounds_codeBufferWrite {B K : Nat} {bounds : BitVec width × BitVec width}
    (r1 r2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  have hp : t.code = s.code ∧ t.compileOracle = s.compileOracle := by
    cases h1 : getVar r1 s with
    | none =>
      rw [evaluate_codeBufferWrite] at h
      simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | some v1 =>
      cases v1 with
      | loc l o =>
        rw [evaluate_codeBufferWrite] at h
        simp only [h1] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | word w1 =>
        cases h2 : getVar r2 s with
        | none =>
          rw [evaluate_codeBufferWrite] at h
          simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
        | some v2 =>
          cases v2 with
          | loc l o =>
            rw [evaluate_codeBufferWrite] at h
            simp only [h1, h2] at h
            obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
          | word w2 =>
            rw [evaluate_codeBufferWrite] at h
            simp only [h1, h2] at h
            cases hw : wordSemBufferWrite s.codeBuffer w1 (BitVec.setWidth 8 w2) with
            | some newCb =>
              simp only [hw] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
            | none =>
              simp only [hw] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  exact codeBounds_transfer hp.1 hp.2 hcode horacle
theorem codeBounds_dataBufferWrite {B K : Nat} {bounds : BitVec width × BitVec width}
    (r1 r2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  by_cases hs : ¬ s.useStack
  · rw [evaluate_dataBufferWrite] at h
    simp only [if_pos hs] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hcode, horacle⟩
  · have hp : t.code = s.code ∧ t.compileOracle = s.compileOracle := by
      cases h1 : getVar r1 s with
      | none =>
        rw [evaluate_dataBufferWrite] at h
        simp only [if_neg hs, h1] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | some v1 =>
        cases v1 with
        | loc l o =>
          rw [evaluate_dataBufferWrite] at h
          simp only [if_neg hs, h1] at h
          obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
        | word w1 =>
          cases h2 : getVar r2 s with
          | none =>
            rw [evaluate_dataBufferWrite] at h
            simp only [if_neg hs, h1, h2] at h
            obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
          | some v2 =>
            cases v2 with
            | loc l o =>
              rw [evaluate_dataBufferWrite] at h
              simp only [if_neg hs, h1, h2] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
            | word w2 =>
              rw [evaluate_dataBufferWrite] at h
              simp only [if_neg hs, h1, h2] at h
              cases hw : wordSemBufferWrite s.dataBuffer w1 w2 with
              | some newCb =>
                simp only [hw] at h
                obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
              | none =>
                simp only [hw] at h
                obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
    exact codeBounds_transfer hp.1 hp.2 hcode horacle
theorem codeBounds_alloc {B K : Nat} {bounds : BitVec width × BitVec width}
    (n : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.alloc n : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hv : getVar n s with
  | none =>
    rw [evaluate_alloc] at h
    simp only [hv] at h
    split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> exact ⟨hcode, horacle⟩
  | some v =>
    cases v with
    | loc l o =>
      rw [evaluate_alloc] at h
      simp only [hv] at h
      split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> exact ⟨hcode, horacle⟩
    | word w =>
      rw [evaluate_alloc] at h
      simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      · have hp := alloc_code w s r t h
        exact codeBounds_transfer hp.1 hp.2 hcode horacle

theorem codeBounds_storeConsts {B K : Nat} {bounds : BitVec width × BitVec width}
    (t1 t2 : Nat) (stubOpt : Option Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.storeConsts t1 t2 stubOpt : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rw [evaluate_storeConsts] at h
  split_ifs at h
  all_goals try (obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩)
  have hp := storeConstSem_code (resultWidth := width) t1 t2 s t (congrArg Prod.snd h)
  exact codeBounds_transfer hp.1 hp.2 hcode horacle

theorem codeBounds_ite {B K : Nat} {bounds : BitVec width × BitVec width}
    (cmp : Cmp) (r1 : Nat) (ri : HolRegImm width) (c1 c2 : HolProg width)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.ite cmp r1 ri c1 c2 : HolProg width), s) = (r, t))
    (ih1 : ∀ r t, evaluate (c1, s) = (r, t) → codeBound B bounds K t ∧ oracleBound B bounds K t)
    (ih2 : ∀ r t, evaluate (c2, s) = (r, t) → codeBound B bounds K t ∧ oracleBound B bounds K t)
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases h1 : getVar r1 s with
  | none =>
    rw [evaluate_ite] at h; simp only [h1] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some x =>
    cases h2 : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
    | none =>
      rw [evaluate_ite] at h; simp only [h1, h2] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | some y =>
      cases hc : wordSemWordCmp cmp x y with
      | none =>
        rw [evaluate_ite] at h; simp only [h1, h2, hc] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      | some b =>
        cases b <;> rw [evaluate_ite] at h <;> simp only [h1, h2, hc] at h
        · exact ih2 r t h
        · exact ih1 r t h

theorem codeBounds_stackLoadAny {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 rn : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackLoadAny r0 rn : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hv : getVar rn s with
  | none =>
    rw [evaluate_stackLoadAny] at h; simp only [hv] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    · obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
  | some v =>
    cases v with
    | loc l o =>
      rw [evaluate_stackLoadAny] at h; simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      · obtain ⟨-, rfl⟩ := h
        exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
    | word w =>
      rw [evaluate_stackLoadAny] at h; simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      · obtain ⟨-, rfl⟩ := h
        exact codeBounds_transfer (setVar_code _ _ _).1 (setVar_code _ _ _).2 hcode horacle
      · obtain ⟨-, rfl⟩ := h
        exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle

theorem codeBounds_stackStoreAny {B K : Nat} {bounds : BitVec width × BitVec width}
    (r0 rn : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackStoreAny r0 rn : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases h1 : getVar r0 s with
  | none =>
    rw [evaluate_stackStoreAny] at h; simp only [h1] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    · obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
  | some value =>
    cases h2 : getVar rn s with
    | none =>
      rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      · obtain ⟨-, rfl⟩ := h
        exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
    | some v =>
      cases v with
      | loc l o =>
        rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
        split_ifs at h
        · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
        · obtain ⟨-, rfl⟩ := h
          exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
      | word w =>
        rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
        split_ifs at h
        · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
        · obtain ⟨-, rfl⟩ := h; exact codeBounds_transfer rfl rfl hcode horacle
        · obtain ⟨-, rfl⟩ := h
          exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle

theorem codeBounds_shMemOp {B K : Nat} {bounds : BitVec width × BitVec width}
    (op : HolMemop) (r0 a : Nat) (w : BitVec width)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.shMemOp op r0 (.addr a w) : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
  | none =>
    rw [evaluate_shMemOp] at h; simp only [ha] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some address =>
    rw [evaluate_shMemOp] at h; simp only [ha] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h
      exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
    · have hh := congrArg Prod.snd h
      have hc := stackShMemOp_code _ _ _ _ _ hh
      have ho := stackShMemOp_oracle _ _ _ _ _ hh
      exact codeBounds_transfer (hc.trans (decClock_code s).1) (ho.trans (decClock_code s).2) hcode horacle

theorem codeBounds_loop {B K : Nat} {bounds : BitVec width × BitVec width}
    (body : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.loop body : HolProg width), s) = (r, t))
    (ihBody : ∀ r t, evaluate (body, s) = (r, t) → codeBound B bounds K t ∧ oracleBound B bounds K t)
    (ihLoop : ∀ (bodyResult : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      evaluate (body, s) = (bodyResult, middle) → middle.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F), evaluate ((.loop body : HolProg width), decClock middle) = (r, t) →
      codeBound B bounds K middle → oracleBound B bounds K middle →
      codeBound B bounds K t ∧ oracleBound B bounds K t)
    : codeBound B bounds K t ∧ oracleBound B bounds K t := by
  rcases he : evaluate (body, s) with ⟨res, post⟩
  have hp := ihBody res post he
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, he] at h
  dsimp only at h
  split_ifs at h with hc hz
  · obtain ⟨-, rfl⟩ := h
    exact codeBounds_transfer (emptyEnv_code post).1 (emptyEnv_code post).2 hp.1 hp.2
  · exact ihLoop res post he hz r t h hp.1 hp.2
  · obtain ⟨-, rfl⟩ := h; exact hp

theorem codeBounds_rawCall {B K : Nat} {bounds : BitVec width × BitVec width}
    (dest : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.rawCall dest : HolProg width), s) = (r, t))
    (ih : ∀ (prog body : HolProg width) (first : HolProg width),
      sptLookup dest s.code = some prog → destSeq prog = some (first, body) →
      ∀ (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F),
      s.clock ≠ 0 → evaluate (body, decClock s) = (res, post) →
      codeBound B bounds K post ∧ oracleBound B bounds K post)
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hc : sptLookup dest s.code with
  | none =>
    rw [evaluate_rawCall] at h; simp only [hc] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some prog =>
    cases hd : destSeq prog with
    | none =>
      rw [evaluate_rawCall] at h; simp only [hc, hd] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | some pair =>
      rcases pair with ⟨first, body⟩
      rw [evaluate_rawCall] at h; simp only [hc, hd] at h
      rcases he : evaluate (body, decClock s) with ⟨res, post⟩
      rw [he] at h
      split_ifs at h with hz hb
      · obtain ⟨-, rfl⟩ := h
        exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
      · obtain ⟨-, rfl⟩ := h; exact ih prog body first hc hd res post hz he
      · obtain ⟨-, rfl⟩ := h; exact ih prog body first hc hd res post hz he

theorem codeBounds_jumpLower {B K : Nat} {bounds : BitVec width × BitVec width}
    (r1 r2 dest : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.jumpLower r1 r2 dest : HolProg width), s) = (r, t))
    (ih : ∀ (prog : HolProg width), findCode (.inl dest) s.regs s.code = some prog →
      ∀ (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F),
      s.clock ≠ 0 → evaluate (prog, decClock s) = (res, post) →
      codeBound B bounds K post ∧ oracleBound B bounds K post)
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases h1 : getVar r1 s with
  | none =>
    rw [evaluate_jumpLower] at h; simp only [h1] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some v1 =>
    cases v1 with
    | loc l o =>
      rw [evaluate_jumpLower] at h; simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | word x =>
      cases h2 : getVar r2 s with
      | none =>
        rw [evaluate_jumpLower] at h; simp only [h1, h2] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      | some v2 =>
        cases v2 with
        | loc l o =>
          rw [evaluate_jumpLower] at h; simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
        | word y =>
          cases hc : findCode (.inl dest) s.regs s.code with
          | none =>
            rw [evaluate_jumpLower] at h; simp only [h1, h2, hc] at h
            split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> exact ⟨hcode, horacle⟩
          | some prog =>
            rcases he : evaluate (prog, decClock s) with ⟨res, post⟩
            rw [evaluate_jumpLower] at h; simp only [h1, h2, hc, he] at h
            split_ifs at h with hcmp hz hb
            · obtain ⟨-, rfl⟩ := h
              exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
            · obtain ⟨-, rfl⟩ := h; exact ih prog hc _ _ hz he
            · obtain ⟨-, rfl⟩ := h; exact ih prog hc _ _ hz he
            · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩

theorem codeBounds_ffi {B K : Nat} {bounds : BitVec width × BitVec width}
    (ffiIndex : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.ffi ffiIndex ptr len ptr2 len2 ret : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases h1 : getVar len s with
  | none =>
    rw [evaluate_ffi] at h; simp only [h1] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some v1 =>
    cases v1 with
    | loc l o =>
      rw [evaluate_ffi] at h; simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | word w1 =>
      cases h2 : getVar ptr s with
      | none =>
        rw [evaluate_ffi] at h; simp only [h1, h2] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      | some v2 =>
        cases v2 with
        | loc l o =>
          rw [evaluate_ffi] at h; simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
        | word w2 =>
          cases h3 : getVar len2 s with
          | none =>
            rw [evaluate_ffi] at h; simp only [h1, h2, h3] at h
            obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
          | some v3 =>
            cases v3 with
            | loc l o =>
              rw [evaluate_ffi] at h; simp only [h1, h2, h3] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
            | word w3 =>
              cases h4 : getVar ptr2 s with
              | none =>
                rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
              | some v4 =>
                cases v4 with
                | loc l o =>
                  rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                  obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                | word w4 =>
                  rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                  cases hb1 : readBytearrayWordHOL w2 w1.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
                  | none =>
                    simp only [hb1] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                  | some bytes =>
                    cases hb2 : readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
                    | none =>
                      simp only [hb1, hb2] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                    | some bytes2 =>
                      cases hf : callFFIHOL s.ffi (.extCall ffiIndex) bytes bytes2 with
                      | final outcome =>
                        simp only [hb1, hb2, hf] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                      | ret newFfi newBytes =>
                        simp only [hb1, hb2, hf] at h; obtain ⟨-, rfl⟩ := h
                        exact codeBounds_transfer rfl rfl hcode horacle

theorem codeBounds_install {B K : Nat} {bounds : BitVec width × BitVec width}
    (ptr len dptr dlen ret : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.install ptr len dptr dlen ret : HolProg width), s) = (r, t))
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  classical
  cases h1 : getVar ptr s with
  | none =>
    rw [evaluate_install] at h; simp only [h1] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
  | some v1 =>
    cases v1 with
    | loc l o =>
      rw [evaluate_install] at h; simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | word w1 =>
      cases h2 : getVar len s with
      | none =>
        rw [evaluate_install] at h; simp only [h1, h2] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      | some v2 =>
        cases v2 with
        | loc l o =>
          rw [evaluate_install] at h; simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
        | word w2 =>
          cases h3 : getVar dptr s with
          | none =>
            rw [evaluate_install] at h; simp only [h1, h2, h3] at h
            obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
          | some v3 =>
            cases v3 with
            | loc l o =>
              rw [evaluate_install] at h; simp only [h1, h2, h3] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
            | word w3 =>
              cases h4 : getVar dlen s with
              | none =>
                rw [evaluate_install] at h; simp only [h1, h2, h3, h4] at h
                obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
              | some v4 =>
                cases v4 with
                | loc l o =>
                  rw [evaluate_install] at h; simp only [h1, h2, h3, h4] at h
                  obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                | word w4 =>
                  rcases hcfg : s.compileOracle 0 with ⟨cfg, progs, bm⟩
                  cases hb1 : wordSemBufferFlush s.codeBuffer w1 w2 with
                  | none =>
                    rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1] at h
                    obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                  | some p1 =>
                    rcases p1 with ⟨bytes, cb⟩
                    cases hb2 : (if s.useStack then wordSemBufferFlush s.dataBuffer w3 w4 else some (bm, s.dataBuffer)) with
                    | none =>
                      rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2] at h
                      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                    | some p2 =>
                      rcases p2 with ⟨data, db⟩
                      cases hcomp : s.compile cfg progs with
                      | none =>
                        rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2, hcomp] at h
                        obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                      | some cp =>
                        rcases cp with ⟨bytes', cfg'⟩
                        cases hp : progs with
                        | nil =>
                          rw [hp] at hcomp
                          rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2, hp, hcomp] at h
                          obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
                        | cons entry rest =>
                          rcases entry with ⟨k, prog⟩
                          rw [hp] at hcomp
                          rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2, hp, hcomp] at h
                          split_ifs at h
                          · obtain ⟨-, rfl⟩ := h
                            constructor
                            · intro label program hl
                              apply install_codeBound s ((k, prog) :: rest) hcode _ label program hl
                              intro name program hm
                              apply horacle 0 name program
                              simpa only [hcfg, hp] using hm
                            · intro index name program hm
                              exact install_oracleBound s horacle index name program hm
                          · obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩

theorem codeBounds_call {B K : Nat} {bounds : BitVec width × BitVec width}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.call ret dest handler : HolProg width), s) = (r, t))
    (ih : ∀ (prog : HolProg width) (start post : StackSemStateFiniteExact width C F)
      (res : Option (StackSemResult width)),
      LexNat (StackSemMeasure.stackSemMeasure prog start)
        (StackSemMeasure.stackSemMeasure (.call ret dest handler) s) →
      evaluate (prog, start) = (res, post) →
      codeBound B bounds K start → oracleBound B bounds K start →
      codeBound B bounds K post ∧ oracleBound B bounds K post)
    (hcode : codeBound B bounds K s) (horacle : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases ret with
  | none =>
    cases hc : findCode dest s.regs s.code with
    | none =>
      rw [evaluate_call] at h; simp only [hc] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | some prog =>
      cases handler with
      | some hd =>
        rw [evaluate_call] at h; simp only [hc] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
      | none =>
        by_cases hz : s.clock = 0
        · rw [evaluate_call] at h; simp only [hc, hz, if_true] at h
          obtain ⟨-, rfl⟩ := h
          exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
        · have hm := StackSemMeasure.callee_measure_lt prog (.call none dest none) s hz
          rcases he : evaluate (prog, decClock s) with ⟨res, post⟩
          have hp := ih prog (decClock s) post res hm he
            (codeBound_congr (decClock_code s).1 hcode) (oracleBound_congr (decClock_code s).2 horacle)
          rw [evaluate_call] at h; simp only [hc, hz, if_false] at h
          rw [StackSemEvaluateClock.fixClockEvaluate, he] at h
          split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> exact hp
  | some retinfo =>
    rcases retinfo with ⟨retHandler, link, l1, l2⟩
    cases hc : findCode dest (s.regs.eraseEq link) s.code with
    | none =>
      rw [evaluate_call] at h; simp only [hc] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨hcode, horacle⟩
    | some prog =>
      by_cases hz : s.clock = 0
      · rw [evaluate_call] at h; simp only [hc, hz, if_true] at h
        obtain ⟨-, rfl⟩ := h
        exact codeBounds_transfer (emptyEnv_code s).1 (emptyEnv_code s).2 hcode horacle
      · let start := decClock (setVar link (.loc l1 l2) s)
        have hs : codeBound B bounds K start ∧ oracleBound B bounds K start := by
          exact codeBounds_transfer ((decClock_code _).1.trans (setVar_code _ _ _).1)
            ((decClock_code _).2.trans (setVar_code _ _ _).2) hcode horacle
        have hs0 : (setVar link (.loc l1 l2) s).clock ≠ 0 := by simpa [setVar] using hz
        have hm := StackSemMeasure.callee_measure_lt prog (.call (some (retHandler, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) s) hs0
        have hpar : StackSemMeasure.stackSemMeasure (.call (some (retHandler, link, l1, l2)) dest handler)
            (setVar link (.loc l1 l2) s) =
            StackSemMeasure.stackSemMeasure (.call (some (retHandler, link, l1, l2)) dest handler) s := by
          simp [StackSemMeasure.stackSemMeasure, setVar]
        rw [hpar] at hm
        rcases he : evaluate (prog, start) with ⟨res, post⟩
        have hp := ih prog start post res hm he hs.1 hs.2
        have hk (cont : HolProg width) :
            LexNat (StackSemMeasure.stackSemMeasure cont post)
              (StackSemMeasure.stackSemMeasure (.call (some (retHandler, link, l1, l2)) dest handler) s) := by
          have hx := StackSemMeasure.call_continuation_measure_lt cont
            (.call (some (retHandler, link, l1, l2)) dest handler) s link l1 l2
            (evaluate (prog, start)) hz
          change LexNat (StackSemMeasure.stackSemMeasure cont
            (fixClock start (evaluate (prog, start))).2) _ at hx
          rw [StackSemEvaluateClock.fixClockEvaluate, he] at hx
          exact hx
        rw [evaluate_call] at h; simp only [hc, hz, if_false] at h
        rw [StackSemEvaluateClock.fixClockEvaluate] at h
        change evaluate (prog, decClock (setVar link (.loc l1 l2) s)) = (res, post) at he
        rw [he] at h
        cases res with
        | none => dsimp only at h; obtain ⟨-, rfl⟩ := h; exact hp
        | some result =>
          cases result <;> dsimp only at h
          all_goals try (obtain ⟨-, rfl⟩ := h; exact hp)
          case result value =>
            split_ifs at h
            · obtain ⟨-, rfl⟩ := h; exact hp
            · exact ih retHandler post t r (hk retHandler) h hp.1 hp.2
          case exception value =>
            cases handler with
            | none =>
              dsimp only at h
              obtain ⟨-, rfl⟩ := h; exact hp
            | some handlerInfo =>
              rcases handlerInfo with ⟨handlerBody, hl1, hl2⟩
              dsimp only at h
              split_ifs at h
              · obtain ⟨-, rfl⟩ := h; exact hp
              · exact ih handlerBody post t r (hk handlerBody) h hp.1 hp.2

theorem codeBounds_evaluate {B K : Nat} {bounds : BitVec width × BitVec width}
    (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (h : evaluate (p, s) = (r, t))
    (hc : codeBound B bounds K s) (ho : oracleBound B bounds K s) :
    codeBound B bounds K t ∧ oracleBound B bounds K t := by
  cases hp : p <;> rw [hp] at h <;> first
    | exact codeBounds_skip _ _ _ h hc ho
    | exact codeBounds_break _ _ _ _ h hc ho
    | exact codeBounds_continue _ _ _ _ h hc ho
    | exact codeBounds_halt _ _ _ _ h hc ho
    | exact codeBounds_tick _ _ _ h hc ho
    | exact codeBounds_ret _ _ _ _ h hc ho
    | exact codeBounds_raise _ _ _ _ h hc ho
    | exact codeBounds_locValue _ _ _ _ _ _ h hc ho
    | exact codeBounds_inst _ _ _ _ h hc ho
    | exact codeBounds_get _ _ _ _ _ h hc ho
    | exact codeBounds_set _ _ _ _ _ h hc ho
    | exact codeBounds_opCurrHeap _ _ _ _ _ _ h hc ho
    | exact codeBounds_stackAlloc _ _ _ _ h hc ho
    | exact codeBounds_stackFree _ _ _ _ h hc ho
    | exact codeBounds_stackLoad _ _ _ _ _ h hc ho
    | exact codeBounds_stackGetSize _ _ _ _ h hc ho
    | exact codeBounds_bitmapLoad _ _ _ _ _ h hc ho
    | exact codeBounds_stackStore _ _ _ _ _ h hc ho
    | exact codeBounds_stackSetSize _ _ _ _ h hc ho
    | exact codeBounds_codeBufferWrite _ _ _ _ _ h hc ho
    | exact codeBounds_dataBufferWrite _ _ _ _ _ h hc ho
    | exact codeBounds_alloc _ _ _ _ h hc ho
    | exact codeBounds_storeConsts _ _ _ _ _ _ h hc ho
    | exact codeBounds_stackLoadAny _ _ _ _ _ h hc ho
    | exact codeBounds_stackStoreAny _ _ _ _ _ h hc ho
    | exact codeBounds_install _ _ _ _ _ _ _ _ h hc ho
    | exact codeBounds_ffi _ _ _ _ _ _ _ _ _ h hc ho
    | skip
  case shMemOp op reg addr =>
    cases addr with
    | addr a w => exact codeBounds_shMemOp op reg a w s t r h hc ho
  case seq a b =>
    apply codeBounds_seq a b s t r h ?_ ?_ hc ho
    · intro rr post hr hca hoa
      exact codeBounds_evaluate a s post rr hr hca hoa
    · intro middle hm rr post hr hcm hom
      have hmle := seq_second_measure_lt a b s (evaluate (a, s))
      rw [StackSemEvaluateClock.fixClockEvaluate, hm] at hmle
      exact codeBounds_evaluate b middle post rr hr hcm hom
  case ite cmp reg ri a b =>
    apply codeBounds_ite cmp reg ri a b s t r h ?_ ?_ hc ho
    · intro rr post hr
      exact codeBounds_evaluate a s post rr hr hc ho
    · intro rr post hr
      exact codeBounds_evaluate b s post rr hr hc ho
  case loop body =>
    apply codeBounds_loop body s t r h ?_ ?_
    · intro rr post hr
      exact codeBounds_evaluate body s post rr hr hc ho
    · intro result middle hm hz rr post hr hcm hom
      have hlt := loop_reentry_measure_lt body s (evaluate (body, s)) (by
        rw [StackSemEvaluateClock.fixClockEvaluate, hm]; exact hz)
      rw [StackSemEvaluateClock.fixClockEvaluate, hm] at hlt
      exact codeBounds_evaluate (.loop body) (decClock middle) post rr hr
        (codeBound_congr (decClock_code middle).1 hcm) (oracleBound_congr (decClock_code middle).2 hom)
  case rawCall dest =>
    apply codeBounds_rawCall dest s t r h ?_ hc ho
    intro prog body first hf hd rr post hz hr
    have hlt := callee_measure_lt body (.rawCall dest) s hz
    exact codeBounds_evaluate body (decClock s) post rr hr
      (codeBound_congr (decClock_code s).1 hc) (oracleBound_congr (decClock_code s).2 ho)
  case jumpLower r1 r2 dest =>
    apply codeBounds_jumpLower r1 r2 dest s t r h ?_ hc ho
    intro prog hf rr post hz hr
    have hlt := callee_measure_lt prog (.jumpLower r1 r2 dest) s hz
    exact codeBounds_evaluate prog (decClock s) post rr hr
      (codeBound_congr (decClock_code s).1 hc) (oracleBound_congr (decClock_code s).2 ho)
  case call ret dest handler =>
    apply codeBounds_call ret dest handler s t r h ?_ hc ho
    intro prog start post rr hlt hr hcs hos
    exact codeBounds_evaluate prog start post rr hr hcs hos
termination_by stackSemMeasure p s
decreasing_by
  all_goals subst p
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate, hm] at hlt)
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate, hm] at hmle)
  all_goals first | assumption | (simpa only [StackSemEvaluateClock.fixClockEvaluate, hm] using hmle) | (simpa only [StackSemEvaluateClock.fixClockEvaluate, hm] using hlt) | exact seq_first_measure_lt _ _ _ | exact if_first_measure_lt _ _ _ _ _ _ | exact if_second_measure_lt _ _ _ _ _ _ | exact loop_body_measure_lt _ _

end SteppedFlapjack.StackRemoveSteps.CompCorrect
