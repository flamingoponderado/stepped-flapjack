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
end SteppedFlapjack.StackRemoveSteps.CompCorrect
