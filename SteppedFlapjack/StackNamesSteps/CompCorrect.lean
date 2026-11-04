import Flapjack.Compiler.Backend.StackNames.Proofs.RenameState
import Flapjack.Compiler.Backend.StackProps.EvaluateConsts
import Flapjack.Misc.Sptree.Wf

/-! Adapted copy of `Flapjack/Compiler/Backend/StackNames/Proofs/CompCorrect.lean`
(stepped-flapjack#2, phase C2). `comp_correct` is copied unchanged, with the
`@[hol]` attributes dropped and the namespace renamed, so that the step
preservation theorem in `SteppedFlapjack.StackNamesSteps.StepsPreservation`
does not import Flapjack's original correctness theorem. `rename_state` and its
definitional lemmas are imported from Flapjack's `Proofs.RenameState`: they are
the pass's state definition and infrastructure, not a correctness result.

`comp_correct` (`stack_namesProofScript.sml:304-526`): renaming the registers of
a program by a bijective `find_name f` commutes with the tagged exact StackSem
`evaluate`, under `rename_state`. HOL proves it by `recInduct evaluate_ind`; here
the induction is the clock-first lexicographic measure that defines `evaluate`,
as for StackProps `evaluate_add_clock`/`evaluate_consts`, with every clause
unfolded by its `evaluate_def` equation.
-/

namespace SteppedFlapjack.StackNamesSteps

open Flapjack Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.StackSemMeasure Flapjack.StackSemEvaluate

namespace CompCorrect

/-- Canonical imported StackSem carrier roundtrip for `comp_correct`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- `MAP_KEYS f FEMPTY = FEMPTY` (Flapjack infrastructure). -/
theorem mapKeys_empty {α β γ : Type} (g : α → γ) :
    HolFiniteMapExact.mapKeys g (HolFiniteMapExact.empty : HolFiniteMapExact α β) =
      HolFiniteMapExact.empty := by
  apply HolFiniteMapExact.ext_lookup
  intro k
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨x, hx, -⟩ := ((HolFiniteMapExact.mapKeys_spec g HolFiniteMapExact.empty).1 k).mp hne
  exact hx rfl

/-- HOL `DOMSUB_MAP_KEYS` for an injective `f` (Flapjack infrastructure). -/
theorem mapKeys_eraseEq {α β γ : Type} [DecidableEq α] [DecidableEq γ] {g : α → γ}
    (hg : Function.Injective g) (m : HolFiniteMapExact α β) (k : α) :
    (HolFiniteMapExact.mapKeys g m).eraseEq (g k) =
      HolFiniteMapExact.mapKeys g (m.eraseEq k) := by
  apply HolFiniteMapExact.ext_lookup
  intro j
  by_cases hj : ∃ x, j = g x
  · obtain ⟨x, rfl⟩ := hj
    rw [HolFiniteMapExact.lookup_mapKeys_of_injective hg]
    simp only [HolFiniteMapExact.eraseEq, FDOMSUB_HOL]
    by_cases hxk : x = k
    · subst hxk; simp
    · rw [if_neg hxk, if_neg (fun h => hxk (hg h)),
        HolFiniteMapExact.lookup_mapKeys_of_injective hg]
  · have hj' : ∀ x, j ≠ g x := fun x h => hj ⟨x, h⟩
    simp only [HolFiniteMapExact.eraseEq, FDOMSUB_HOL]
    rw [if_neg (hj' k)]
    rw [show (HolFiniteMapExact.mapKeys g m).lookup j = none from
        HolFiniteMapExact.lookup_mapKeys_of_not_range _ hj']
    exact (HolFiniteMapExact.lookup_mapKeys_of_not_range _ hj').symm

/-- HOL `DRESTRICT_MAP_KEYS_IMAGE` for an injective `f`, on the Boolean saved-register mask
(Flapjack infrastructure). -/
theorem mapKeys_restrictIn {α β γ : Type} {g : α → γ} (hg : Function.Injective g)
    (m : HolFiniteMapExact α β) (keep : α → Bool) :
    open Classical in
    restrictIn (HolFiniteMapExact.mapKeys g m) (fun y => decide (∃ x, keep x = true ∧ y = g x)) =
      HolFiniteMapExact.mapKeys g (restrictIn m keep) := by
  apply HolFiniteMapExact.ext_lookup
  intro j
  rw [restrictIn_lookup]
  by_cases hj : ∃ x, j = g x
  · obtain ⟨x, rfl⟩ := hj
    rw [HolFiniteMapExact.lookup_mapKeys_of_injective hg,
      HolFiniteMapExact.lookup_mapKeys_of_injective hg, restrictIn_lookup]
    by_cases hk : keep x = true
    · have he : ∃ y, keep y = true ∧ g x = g y := ⟨x, hk, rfl⟩
      simp [he, hk]
    · have he : ¬ ∃ y, keep y = true ∧ g x = g y := fun ⟨y, hy, hxy⟩ => hk (hg hxy ▸ hy)
      simp [he, hk]
  · have hj' : ∀ x, j ≠ g x := fun x h => hj ⟨x, h⟩
    rw [HolFiniteMapExact.lookup_mapKeys_of_not_range _ hj',
      HolFiniteMapExact.lookup_mapKeys_of_not_range _ hj']
    split <;> rfl

section RenameFacts
variable {width : Nat} [NeZero width] {C F : Type}
  {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}

@[simp] theorem renameState_useAlloc (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).useAlloc = s.useAlloc := rfl
@[simp] theorem renameState_useStore (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).useStore = s.useStore := rfl
@[simp] theorem renameState_useStack (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).useStack = s.useStack := rfl
@[simp] theorem renameState_clock (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).clock = s.clock := rfl

theorem emptyEnv_renameState (s : StackSemStateFiniteExact width C F) :
    emptyEnv (renameState c f s) = renameState c f (emptyEnv s) := by
  simp only [emptyEnv, renameState]
  rw [mapKeys_empty]; rfl

theorem fixClock_renameState (s t : StackSemStateFiniteExact width C F) {R : Type} (r : R) :
    fixClock (renameState c f s) (r, renameState c f t) =
      (r, renameState c f (fixClock s (r, t)).2) := rfl

end RenameFacts

section RenameFacts2
variable {width : Nat} [NeZero width] {C F : Type}
  {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}

@[simp] theorem renameState_codeBuffer (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).codeBuffer = s.codeBuffer := rfl
@[simp] theorem renameState_dataBuffer (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).dataBuffer = s.dataBuffer := rfl
@[simp] theorem renameState_memory (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).memory = s.memory := rfl
@[simp] theorem renameState_mdomain (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).mdomain = s.mdomain := rfl
@[simp] theorem renameState_be (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).be = s.be := rfl
@[simp] theorem renameState_ffi (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).ffi = s.ffi := rfl

/-- The FFI return update commutes with renaming (Flapjack infrastructure, from
`DRESTRICT_MAP_KEYS_IMAGE`). -/
theorem renameState_ffiReturn (hf : Function.Injective (findNameSpt f))
    (s : StackSemStateFiniteExact width C F) (m : BitVec width → WordLocW width)
    (ffi' : HolFfiState F) :
    renameState c f { s with
        memory := m
        regs := restrictIn s.regs s.ffiSaveRegs
        fpRegs := HolFiniteMapExact.empty
        ffi := ffi' } =
      { renameState c f s with
        memory := m
        regs := restrictIn (renameState c f s).regs (renameState c f s).ffiSaveRegs
        fpRegs := HolFiniteMapExact.empty
        ffi := ffi' } := by
  simp only [renameState]
  rw [mapKeys_restrictIn hf]

end RenameFacts2

/-- `dest_Seq` through `comp` (Flapjack infrastructure). -/
theorem destSeq_progCompHOL {width : Nat} [NeZero width] (f : Spt Nat) (p : HolProg width) :
    destSeq (progCompHOL f p) = (destSeq p).map (Prod.map (progCompHOL f) (progCompHOL f)) := by
  cases p <;> try rfl
  case call rh d hd =>
    rcases rh with _ | ⟨_, _, _, _⟩ <;> rcases hd with _ | ⟨_, _, _⟩ <;> rfl

/-- The handler argument of `comp` on `Call` (Flapjack infrastructure). -/
def handlerComp {width : Nat} [NeZero width] (f : Spt Nat) :
    Option (HolProg width × Nat × Nat) → Option (HolProg width × Nat × Nat)
  | none => none
  | some (hp, a, b) => some (progCompHOL f hp, a, b)

theorem progCompHOL_callSome {width : Nat} [NeZero width] (f : Spt Nat) (retH : HolProg width)
    (link l1 l2 : Nat) (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat)) :
    progCompHOL f (.call (some (retH, link, l1, l2)) dest handler) =
      .call (some (progCompHOL f retH, findNameSpt f link, l1, l2)) (destFindNameHOL f dest)
        (handlerComp f handler) := by
  rcases handler with _ | ⟨_, _, _⟩ <;> rfl

/-- The renamed code of a code union (Flapjack infrastructure, from `spt_eq_thm`,
`lookup_union`, `lookup_fromAList`, `ALOOKUP_MAP` and `ALOOKUP_toAList`). -/
theorem renamedCode_union {width : Nat} [NeZero width] (f : Spt Nat) (code : Spt (HolProg width))
    (progs : List (Nat × HolProg width)) :
    sptFromAList (compileHOL f (sptToAList (sptUnion code (sptFromAList progs)))) =
      sptUnion (sptFromAList (compileHOL f (sptToAList code))) (sptFromAList (compileHOL f progs)) := by
  have hL : ∀ (t : Spt (HolProg width)) n,
      sptLookup n (sptFromAList (compileHOL f (sptToAList t))) = (sptLookup n t).map (progCompHOL f) := by
    intro t n
    rw [sptLookup_sptFromAList, sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
      sptLookup_sptFromAList_sptToAList]
  refine (sptEqThm _ _ ⟨sptWfFromAList _,
    sptWfUnion _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩⟩).mpr fun n => ?_
  rw [hL, sptLookup_sptUnion, sptLookup_sptUnion, hL, sptLookup_sptFromAList,
    sptLookup_sptFromAList, sptAListLookup_compileHOL]
  cases sptLookup n code <;> rfl

/-- The `comp_correct` premises on a source state (Flapjack infrastructure). -/
def Pre {width : Nat} [NeZero width] {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (s : StackSemStateFiniteExact width C F) : Prop :=
  ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧ s.compile = fun cfg => c cfg ∘ compileHOL f

theorem Pre.of_evaluate {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {p : HolProg width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} (h : evaluate (p, s) = (r, t)) (hs : Pre c f s) :
    Pre c f t := by
  obtain ⟨a, b, k, -, -, -, -, e⟩ :=
    Flapjack.Compiler.Backend.StackProps.evaluateConsts p s r t h
  obtain ⟨ha, hb, hk, he⟩ := hs
  exact ⟨a ▸ ha, b ▸ hb, k ▸ hk, e ▸ he⟩

/-- The induction on HOL's `evaluate` measure, carrying the `comp_correct` statement. -/
theorem comp_measure {width : Nat} [NeZero width] {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (findNameSpt f)) :
    ∀ (m : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = m → ∀ (r : Option (StackSemResult width))
        (t : StackSemStateFiniteExact width C F),
      evaluate (p, s) = (r, t) → Pre c f s →
      evaluate (progCompHOL f p, renameState c f s) = (r, renameState c f t) := by
  intro m
  induction m using Flapjack.Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ m ih =>
  intro p s hm r t h hpre
  subst hm
  have hpre' := hpre
  obtain ⟨hA, hS, hK, hC⟩ := hpre'
  simp only [Bool.not_eq_true] at hA hS hK
  cases p
  case skip => rw [evaluate_skip] at h; cases h; exact evaluate_skip _
  case «break» v => rw [evaluate_break] at h; cases h; exact evaluate_break _ _
  case «continue» v => rw [evaluate_continue] at h; cases h; exact evaluate_continue _ _
  case halt v =>
    change evaluate (.halt (findNameSpt f v), _) = _
    rw [evaluate_halt] at h; rw [evaluate_halt, getVar_findName hf]
    cases hv : getVar v s <;> simp only [hv, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · rfl
    · simp only [emptyEnv_renameState]
  case ret v =>
    change evaluate (.ret (findNameSpt f v), _) = _
    rw [evaluate_ret] at h; rw [evaluate_ret, getVar_findName hf]
    rcases hv : getVar v s with _ | ⟨_ | ⟨l1, l2⟩⟩ <;> simp only [hv, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> rfl
  case raise v =>
    change evaluate (.raise (findNameSpt f v), _) = _
    rw [evaluate_raise] at h; rw [evaluate_raise, getVar_findName hf]
    rcases hv : getVar v s with _ | ⟨_ | ⟨l1, l2⟩⟩ <;> simp only [hv, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> rfl
  case tick =>
    change evaluate (.tick, _) = _
    rw [evaluate_tick] at h; rw [evaluate_tick, renameState_clock]
    by_cases h0 : s.clock = 0 <;> simp only [h0, if_true, if_false, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · simp only [h0, if_true, emptyEnv_renameState]
    · simp only [h0, if_false]; rfl
  case alloc n =>
    change evaluate (.alloc n, _) = _
    rw [evaluate_alloc] at h; rw [evaluate_alloc]
    simp only [renameState_useAlloc, hA, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case get v n =>
    change evaluate (.get v n, _) = _
    rw [evaluate_get] at h; rw [evaluate_get]
    simp only [renameState_useStore, hS, Bool.false_eq_true, not_false_eq_true, if_true,
      Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case set n v =>
    change evaluate (.set n v, _) = _
    rw [evaluate_set] at h; rw [evaluate_set]
    simp only [renameState_useStore, hS, Bool.false_eq_true, not_false_eq_true, if_true,
      Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case opCurrHeap b d src =>
    change evaluate (.opCurrHeap b d src, _) = _
    rw [evaluate_opCurrHeap] at h; rw [evaluate_opCurrHeap]
    simp only [renameState_useStore, hS, Bool.false_eq_true, not_false_eq_true, if_true,
      Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case storeConsts t1 t2 stub =>
    change evaluate (.storeConsts t1 t2 stub, _) = _
    rw [evaluate_storeConsts] at h; rw [evaluate_storeConsts]
    simp only [renameState_useStore, hS, Bool.false_eq_true, not_false_eq_true, if_true,
      Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackAlloc n =>
    change evaluate (.stackAlloc n, _) = _
    rw [evaluate_stackAlloc] at h; rw [evaluate_stackAlloc]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackFree n =>
    change evaluate (.stackFree n, _) = _
    rw [evaluate_stackFree] at h; rw [evaluate_stackFree]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackLoad a b =>
    change evaluate (.stackLoad a b, _) = _
    rw [evaluate_stackLoad] at h; rw [evaluate_stackLoad]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackLoadAny a b =>
    change evaluate (.stackLoadAny a b, _) = _
    rw [evaluate_stackLoadAny] at h; rw [evaluate_stackLoadAny]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackStore a b =>
    change evaluate (.stackStore a b, _) = _
    rw [evaluate_stackStore] at h; rw [evaluate_stackStore]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackStoreAny a b =>
    change evaluate (.stackStoreAny a b, _) = _
    rw [evaluate_stackStoreAny] at h; rw [evaluate_stackStoreAny]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackGetSize a =>
    change evaluate (.stackGetSize a, _) = _
    rw [evaluate_stackGetSize] at h; rw [evaluate_stackGetSize]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case stackSetSize a =>
    change evaluate (.stackSetSize a, _) = _
    rw [evaluate_stackSetSize] at h; rw [evaluate_stackSetSize]
    simp only [renameState_useStack, hK, Bool.not_false, if_true, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case bitmapLoad a b =>
    change evaluate (.bitmapLoad a b, _) = _
    rw [evaluate_bitmapLoad] at h; rw [evaluate_bitmapLoad]
    simp only [renameState_useStack, hK, Bool.not_false, Bool.true_or, if_true,
      Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case dataBufferWrite a b =>
    change evaluate (.dataBufferWrite a b, _) = _
    rw [evaluate_dataBufferWrite] at h; rw [evaluate_dataBufferWrite]
    simp only [renameState_useStack, hK, Bool.false_eq_true, not_false_eq_true, if_true,
      Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case inst i =>
    change evaluate (.inst (instFindNameHOL f i), _) = _
    rw [evaluate_inst] at h; rw [evaluate_inst, instRename hf]
    rcases hi : StackSemInst.instHOL i s with _ | u <;> simp only [hi, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> rfl
  case locValue a l1 l2 =>
    change evaluate (.locValue (findNameSpt f a) l1 l2, _) = _
    rw [evaluate_locValue] at h; rw [evaluate_locValue, locCheck_renameState]
    by_cases hl : StackSem.locCheckExact s.code (l1, l2) <;>
      simp only [hl, if_true, if_false, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · simp only [hl, if_true, setVar_findName hf]
    · simp only [hl, if_false]
  case codeBufferWrite a b =>
    change evaluate (.codeBufferWrite (findNameSpt f a) (findNameSpt f b), _) = _
    rw [evaluate_codeBufferWrite] at h
    rw [evaluate_codeBufferWrite, getVar_findName hf, getVar_findName hf, renameState_codeBuffer]
    rcases ha : getVar a s with _ | ⟨wa | _⟩ <;> rcases hb : getVar b s with _ | ⟨wb | _⟩ <;>
      simp only [ha, hb, Prod.mk.injEq] at h <;> try (obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases hw : wordSemBufferWrite s.codeBuffer wa (wb.setWidth 8) with _ | cb <;>
      simp only [hw] at h ⊢ <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> rfl
  case shMemOp op reg addr =>
    cases addr with
    | addr a w =>
    change evaluate (.shMemOp op (findNameSpt f reg) (.addr (findNameSpt f a) w), _) = _
    rw [evaluate_shMemOp] at h; rw [evaluate_shMemOp, wordExp_addr_renameState hf, renameState_clock]
    rcases he : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with _ | a' <;>
      simp only [he] at h ⊢
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    · by_cases h0 : s.clock = 0 <;> simp only [h0, if_true, if_false] at h ⊢
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp only [emptyEnv_renameState]
      · rw [decClock_renameState, shMemOp_renameState hf, h]
  case seq c1 c2 =>
    change evaluate (.seq (progCompHOL f c1) (progCompHOL f c2), _) = _
    rw [evaluate_seq] at h; rw [evaluate_seq]
    rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
    have e1 := ih _ (seq_first_measure_lt c1 c2 s) c1 s rfl r1 t1 h1 hpre
    rw [h1] at h; rw [e1, fixClock_renameState]
    have hfx : fixClock s (r1, t1) = (r1, { t1 with clock := min s.clock t1.clock }) := rfl
    rw [hfx] at h ⊢
    cases r1 with
    | none =>
      have hlt := seq_second_measure_lt c1 c2 s ((none : Option (StackSemResult width)), t1)
      rw [hfx] at hlt
      have hp1 : Pre c f t1 := Pre.of_evaluate h1 hpre
      exact ih _ hlt c2 _ rfl r t h hp1
    | some x =>
      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  case ite cmp r1 ri c1 c2 =>
    change evaluate (.ite cmp (findNameSpt f r1) (riFindNameHOL f ri) (progCompHOL f c1)
      (progCompHOL f c2), _) = _
    rw [evaluate_ite] at h; rw [evaluate_ite, getVar_findName hf, getVarImm_findName hf]
    rcases hx : getVar r1 s with _ | x <;>
      rcases hy : StackSemStateOps.getVarImm ri.toWordRegImm s with _ | y <;>
      simp only [hx, hy] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases hc : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hc] at h ⊢
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    · exact ih _ (if_second_measure_lt cmp r1 ri c1 c2 s) c2 s rfl r t h hpre
    · exact ih _ (if_first_measure_lt cmp r1 ri c1 c2 s) c1 s rfl r t h hpre
  case loop c1 =>
    change evaluate (.loop (progCompHOL f c1), _) = _
    rw [evaluate_loop] at h; rw [evaluate_loop]
    rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
    have e1 := ih _ (loop_body_measure_lt c1 s) c1 s rfl r1 t1 h1 hpre
    rw [h1] at h; rw [e1, fixClock_renameState]
    have hfx : fixClock s (r1, t1) = (r1, { t1 with clock := min s.clock t1.clock }) := rfl
    rw [hfx] at h ⊢
    dsimp only at h ⊢
    by_cases hl : StackSemControl.contLoop r1 = true
    · simp only [hl, if_true] at h ⊢
      by_cases h0 : min s.clock t1.clock = 0
      · simp only [renameState_clock, h0, if_true, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, emptyEnv_renameState _⟩
      · simp only [renameState_clock, h0, if_false] at h ⊢
        have hlt := loop_reentry_measure_lt c1 s (r1, t1) (by rw [hfx]; exact h0)
        rw [hfx] at hlt
        rw [decClock_renameState]
        have hp1 : Pre c f t1 := Pre.of_evaluate h1 hpre
        exact ih _ hlt (.loop c1) _ rfl r t h hp1
    · simp only [hl, Bool.false_eq_true, if_false, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case ffi n p1 p2 p3 p4 p5 =>
    change evaluate (.ffi n (findNameSpt f p1) (findNameSpt f p2) (findNameSpt f p3)
      (findNameSpt f p4) (findNameSpt f p5), _) = _
    rw [evaluate_ffi] at h; rw [evaluate_ffi]
    simp only [getVar_findName hf, renameState_memory, renameState_mdomain, renameState_be,
      renameState_ffi]
    rcases h2 : getVar p2 s with _ | ⟨w | _⟩ <;> simp only [h2] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases h1 : getVar p1 s with _ | ⟨w2 | _⟩ <;> simp only [h1] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases h4 : getVar p4 s with _ | ⟨w3 | _⟩ <;> simp only [h4] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases h3 : getVar p3 s with _ | ⟨w4 | _⟩ <;> simp only [h3] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases hb1 : readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s.memory s.mdomain s.be)
      with _ | bytes <;> simp only [hb1] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases hb2 : readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be)
      with _ | bytes2 <;> simp only [hb2] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    cases hcall : callFFIHOL s.ffi (.extCall n) bytes bytes2 <;> simp only [hcall] at h ⊢ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    all_goals first | rfl | exact congrArg (Prod.mk none) (renameState_ffiReturn hf.1 s _ _).symm
  case jumpLower r1 r2 dest =>
    change evaluate (.jumpLower (findNameSpt f r1) (findNameSpt f r2) dest, _) = _
    rw [evaluate_jumpLower] at h
    rw [evaluate_jumpLower, getVar_findName hf, getVar_findName hf]
    rcases hx : getVar r1 s with _ | ⟨x | _⟩ <;> simp only [hx] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases hy : getVar r2 s with _ | ⟨y | _⟩ <;> simp only [hy] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    by_cases hw : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower x y = true
    · simp only [hw, if_true] at h ⊢
      have hfc : findCode (.inl dest) (renameState c f s).regs (renameState c f s).code =
          (findCode (.inl dest) s.regs s.code).map (progCompHOL f) :=
        findCode_renameState (dest := .inl dest) hf
      rw [hfc]
      rcases hp : findCode (.inl dest) s.regs s.code with _ | prog <;>
        simp only [hp, Option.map_none, Option.map_some] at h ⊢
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
      by_cases h0 : s.clock = 0
      · simp only [renameState_clock, h0, if_true, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, emptyEnv_renameState _⟩
      simp only [renameState_clock, h0, if_false] at h ⊢
      rcases h1 : evaluate (prog, decClock s) with ⟨r1', t1⟩
      have e1 := ih _ (callee_measure_lt prog _ s h0) prog _ rfl r1' t1 h1 hpre
      rw [h1] at h; rw [decClock_renameState, e1]
      dsimp only at h ⊢
      by_cases hb : badFunReturn r1' = true <;>
        simp only [hb, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq] at h ⊢ <;>
        obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩
    · simp only [hw, Bool.false_eq_true, if_false, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case rawCall dest =>
    change evaluate (.rawCall dest, _) = _
    rw [evaluate_rawCall] at h; rw [evaluate_rawCall, sptLookup_renameState_code]
    rcases hp : sptLookup dest s.code with _ | prog <;>
      simp only [hp, Option.map_none, Option.map_some] at h ⊢
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    rw [destSeq_progCompHOL]
    rcases hd : destSeq prog with _ | ⟨a, body⟩ <;>
      simp only [hd, Option.map_none, Option.map_some, Prod.map] at h ⊢
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    by_cases h0 : s.clock = 0
    · simp only [renameState_clock, h0, if_true, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, emptyEnv_renameState _⟩
    simp only [renameState_clock, h0, if_false] at h ⊢
    rcases h1 : evaluate (body, decClock s) with ⟨r1', t1⟩
    have e1 := ih _ (callee_measure_lt body _ s h0) body _ rfl r1' t1 h1 hpre
    rw [h1] at h; rw [decClock_renameState, e1]
    dsimp only at h ⊢
    by_cases hb : badFunReturn r1' = true <;>
      simp only [hb, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq] at h ⊢ <;>
      obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩
  case call ret dest handler =>
    rcases ret with _ | ⟨retH, link, l1, l2⟩
    · rcases handler with _ | ⟨hp, hl1, hl2⟩
      · change evaluate (.call none (destFindNameHOL f dest) none, _) = _
        rw [evaluate_call] at h; rw [evaluate_call]
        dsimp only at h ⊢
        rw [findCode_renameState hf]
        rcases hpc : findCode dest s.regs s.code with _ | prog <;>
          simp only [hpc, Option.map_none, Option.map_some] at h ⊢
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        by_cases h0 : s.clock = 0
        · simp only [renameState_clock, h0, if_true, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, emptyEnv_renameState _⟩
        simp only [renameState_clock, h0, if_false] at h ⊢
        rcases h1 : evaluate (prog, decClock s) with ⟨r1', t1⟩
        have e1 := ih _ (callee_measure_lt prog _ s h0) prog _ rfl r1' t1 h1 hpre
        rw [h1] at h; rw [decClock_renameState, e1, fixClock_renameState]
        have hfx : fixClock (decClock s) (r1', t1) =
            (r1', { t1 with clock := min (decClock s).clock t1.clock }) := rfl
        rw [hfx] at h ⊢
        dsimp only at h ⊢
        by_cases hb : badFunReturn r1' = true <;>
          simp only [hb, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq] at h ⊢ <;>
          obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩
      · change evaluate (.call none (destFindNameHOL f dest)
          (some (progCompHOL f hp, hl1, hl2)), _) = _
        rw [evaluate_call] at h; rw [evaluate_call]
        dsimp only at h ⊢
        rw [findCode_renameState hf]
        rcases hpc : findCode dest s.regs s.code with _ | prog <;>
          simp only [hpc, Option.map_none, Option.map_some, Prod.mk.injEq] at h ⊢ <;>
          obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩
    · rw [progCompHOL_callSome]
      rw [evaluate_call] at h; rw [evaluate_call]
      dsimp only at h ⊢
      have hfc : findCode (destFindNameHOL f dest)
          ((renameState c f s).regs.eraseEq (findNameSpt f link)) (renameState c f s).code =
          (findCode dest (s.regs.eraseEq link) s.code).map (progCompHOL f) := by
        have := findCode_renameState (c := c) (s := { s with regs := s.regs.eraseEq link })
          (dest := dest) hf
        rw [← this]
        show _ = findCode _ (HolFiniteMapExact.mapKeys (findNameSpt f) (s.regs.eraseEq link)) _
        rw [← mapKeys_eraseEq hf.1]; rfl
      rw [hfc]
      rcases hpc : findCode dest (s.regs.eraseEq link) s.code with _ | prog <;>
        simp only [hpc, Option.map_none, Option.map_some] at h ⊢
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
      by_cases h0 : s.clock = 0
      · simp only [renameState_clock, h0, if_true, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, emptyEnv_renameState _⟩
      simp only [renameState_clock, h0, if_false] at h ⊢
      rw [← setVar_findName hf]
      have h0' : (setVar link (.loc l1 l2) s).clock ≠ 0 := h0
      have hpv : Pre c f (decClock (setVar link (.loc l1 l2) s)) := hpre
      rcases h1 : evaluate (prog, decClock (setVar link (.loc l1 l2) s)) with ⟨r1', t1⟩
      have e1 := ih _ (lexNat_decClock (setVar link (.loc l1 l2) s) _ _ h0') prog _ rfl r1' t1
        h1 hpv
      rw [h1] at h; rw [decClock_renameState, e1, fixClock_renameState]
      have hfx : fixClock (decClock (setVar link (.loc l1 l2) s)) (r1', t1) =
          (r1', { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock }) :=
        rfl
      have hlt := fun cont => call_continuation_measure_lt cont
        (.call (some (retH, link, l1, l2)) dest handler) s link l1 l2 (r1', t1) h0
      rw [hfx] at h hlt ⊢
      have hp1 : Pre c f t1 := Pre.of_evaluate h1 hpv
      dsimp only at h ⊢
      rcases r1' with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
      all_goals try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      · by_cases hx : x = .loc l1 l2
        · simp only [hx, ne_eq, not_true_eq_false, if_false] at h ⊢
          exact ih _ (hlt retH) retH _ rfl r t h hp1
        · simp only [hx, ne_eq, not_false_eq_true, if_true, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      · rcases handler with _ | ⟨hp, hl1, hl2⟩
        · dsimp only [handlerComp] at h ⊢
          simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · dsimp only [handlerComp] at h ⊢
          by_cases hx : x = .loc hl1 hl2
          · simp only [hx, ne_eq, not_true_eq_false, if_false] at h ⊢
            exact ih _ (hlt hp) hp _ rfl r t h hp1
          · simp only [hx, ne_eq, not_false_eq_true, if_true, Prod.mk.injEq] at h ⊢
            obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case install p1 p2 p3 p4 p5 =>
    change evaluate (.install (findNameSpt f p1) (findNameSpt f p2) (findNameSpt f p3)
      (findNameSpt f p4) (findNameSpt f p5), _) = _
    rcases hor : s.compileOracle 0 with ⟨cfg, progs, bm⟩
    have hor' : (renameState c f s).compileOracle 0 = (cfg, compileHOL f progs, bm) := by
      show Prod.map id (Prod.map (compileHOL f) id) (s.compileOracle 0) = _
      rw [hor]; rfl
    rw [evaluate_install] at h; rw [evaluate_install]
    rw [hor']; rw [hor] at h
    simp only [getVar_findName hf]
    rcases h1 : getVar p1 s with _ | ⟨w1 | _⟩ <;> simp only [h1] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases h2 : getVar p2 s with _ | ⟨w2 | _⟩ <;> simp only [h2] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases h3 : getVar p3 s with _ | ⟨w3 | _⟩ <;> simp only [h3] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    rcases h4 : getVar p4 s with _ | ⟨w4 | _⟩ <;> simp only [h4] at h ⊢ <;>
      try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    try dsimp only at h ⊢
    simp only [renameState_codeBuffer, renameState_useStack, hK, Bool.false_eq_true, if_false]
      at h ⊢
    rcases hfl : wordSemBufferFlush s.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩ <;>
      simp only [hfl] at h ⊢
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    rw [hC] at h
    have hcomp : (renameState c f s).compile = c := rfl
    rw [hcomp]
    dsimp only [Function.comp] at h
    rcases hcm : c cfg (compileHOL f progs) with _ | ⟨bytes', cfg'⟩ <;> simp only [hcm] at h ⊢
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    rcases progs with _ | ⟨⟨k, prog⟩, rest⟩
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    have hcl : compileHOL f ((k, prog) :: rest) = (k, progCompHOL f prog) :: compileHOL f rest :=
      rfl
    rw [hcl]
    dsimp only at h ⊢
    have hno : (holShiftSeq 1 (renameState c f s).compileOracle 0).1 =
        (holShiftSeq 1 s.compileOracle 0).1 := rfl
    rw [hno]
    split at h
    · rename_i hcond
      rw [if_pos hcond]
      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine congrArg (Prod.mk none) ?_
      simp only [renameState]
      rw [HolFiniteMapExact.mapKeys_updateEq hf.1, ← mapKeys_restrictIn hf.1, ← hcl,
        renamedCode_union]
      rfl
    · rename_i hcond
      rw [if_neg hcond]
      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

end CompCorrect

/-- Exact HOL `comp_correct` (`stack_namesProofScript.sml:304-526`, `[local]`): for a bijective
`find_name f`, without allocation, store or stack use, and with `s.compile` factoring through
`stack_names$compile f`, evaluating the renamed program from the renamed state yields the same
result and the renamed final state. HOL's free `f` and `c` are the implicit binders. -/
theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} :
    ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F)
      (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
      evaluate (p, s) = (r, t) ∧ Function.Bijective (findNameSpt f) ∧
        ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧
        s.compile = (fun cfg => c cfg ∘ compileHOL f) →
      evaluate (progCompHOL f p, renameState c f s) = (r, renameState c f t) :=
  fun p s r t ⟨h, hf, ha, hs, hk, hc⟩ =>
    CompCorrect.comp_measure c f hf _ p s rfl r t h ⟨ha, hs, hk, hc⟩

end SteppedFlapjack.StackNamesSteps
