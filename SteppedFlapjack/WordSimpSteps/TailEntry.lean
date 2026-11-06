import SteppedFlapjack.LoopLiveSteps.TailEntryShape
import SteppedFlapjack.WordSimpSteps.LoopSequenceCompile

/-! WordSimp preprocessing of direct tail-entry programs. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp
open SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

theorem smartSeq_tailEntry {a b : WordLangProgHOL (BitVec width)}
    (ha : WordTailEntryShape a) (hb : WordTailEntryShape b) :
    WordTailEntryShape (Compiler.Backend.WordSimp.smartSeqHOL a b) := by
  cases a <;> simp only [Compiler.Backend.WordSimp.smartSeqHOL] <;> first | exact hb | exact .seq ha hb

/-- Sequence reassociation keeps the direct call and all branch prefixes. -/
theorem seqAssoc_tailEntry {p : WordLangProgHOL (BitVec width)} (hp : WordTailEntryShape p) :
    ∀ {prelude}, WordTailEntryShape prelude → WordTailEntryShape (Compiler.Backend.WordSimp.seqAssoc prelude p) := by
  induction hp with
  | branch hp =>
    intro prelude pre
    induction hp generalizing prelude with
    | skip => simpa only [Compiler.Backend.WordSimp.seqAssoc] using pre
    | seq ha hb iha ihb => simp only [Compiler.Backend.WordSimp.seqAssoc]; exact ihb (iha pre)
    | ite cmp r ri ha hb iha ihb =>
      simp only [Compiler.Backend.WordSimp.seqAssoc]
      exact smartSeq_tailEntry pre (.branch (.ite cmp r ri (seqAssoc_branch ha .skip) (seqAssoc_branch hb .skip)))
    | assign dst e => exact smartSeq_tailEntry pre (.branch (.assign dst e))
    | inst i => exact smartSeq_tailEntry pre (.branch (.inst i))
    | move pri ms => exact smartSeq_tailEntry pre (.branch (.move pri ms))
    | get dst n => exact smartSeq_tailEntry pre (.branch (.get dst n))
    | opCurrHeap op dst src => exact smartSeq_tailEntry pre (.branch (.opCurrHeap op dst src))
    | set n e => exact smartSeq_tailEntry pre (.branch (.set n e))
    | store e src => exact smartSeq_tailEntry pre (.branch (.store e src))
    | tick => exact smartSeq_tailEntry pre (.branch .tick)
    | ret r vs => exact smartSeq_tailEntry pre (.branch (.ret r vs))
    | «break» n => exact smartSeq_tailEntry pre (.branch (.break n))
    | «continue» n => exact smartSeq_tailEntry pre (.branch (.continue n))
  | call loc => intro prelude pre; exact smartSeq_tailEntry pre (.call loc)
  | seq ha hb iha ihb => intro prelude pre; simp only [Compiler.Backend.WordSimp.seqAssoc]; exact ihb (iha pre)

/-- Materializing constant arguments produces only supported branch code. -/
theorem dropConsts_branch (cs : Spt (BitVec width)) (args : List Nat) : Branch (dropConsts cs args) := by
  induction args with
  | nil => exact .skip
  | cons n ns ih =>
    simp only [dropConsts]
    cases h : sptLookup n cs with
    | none => simpa only [h] using ih
    | some w => simpa only [h] using smartSeq_branch ih (.assign n (.const w))

/-- Constant propagation may materialize the return-location argument, while
preserving the direct call and supported branch shape. -/
theorem constFpLoop_tailEntry {p : WordLangProgHOL (BitVec width)} (hp : WordTailEntryShape p) :
    ∀ cs, WordTailEntryShape (constFpLoop p cs).1 := by
  induction hp with
  | branch hp => intro cs; exact .branch (constFpLoop_branch hp cs)
  | call loc => intro cs; exact smartSeq_tailEntry (.branch (dropConsts_branch cs [0])) (.call loc)
  | @seq a b ha hb iha ihb =>
    intro cs
    simp only [constFpLoop]
    rcases h : constFpLoop a cs with ⟨a',ca⟩
    rcases k : constFpLoop b ca with ⟨b',cb⟩
    have aa := iha cs
    have bb := ihb ca
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb

omit [NeZero width] in
theorem tailEntry_ite_inv (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (h : WordTailEntryShape (.ite cmp r ri a b)) : Branch a ∧ Branch b := by
  cases h with
  | branch h => cases h with | ite _ _ _ ha hb => exact ⟨ha,hb⟩

theorem tryIfHoist2_tailEntry (fuel : Nat) : ∀
    {p interm dummy after out : WordLangProgHOL (BitVec width)},
    WordTailEntryShape p → Branch interm → Branch after →
    tryIfHoist2 fuel p interm dummy after = some out → WordTailEntryShape out := by
  induction fuel with
  | zero => intros; simp_all [tryIfHoist2]
  | succ fuel ih =>
    intro p interm dummy after out hp hi ht h
    cases hp with
    | branch hp => exact .branch (tryIfHoist2_branch _ hp hi ht h)
    | call loc => simp [tryIfHoist2] at h
    | @seq a b ha hb =>
      simp only [tryIfHoist2] at h
      cases hd : destIf b with
      | none =>
        simp only [hd] at h
        split at h
        · rename_i simple
          exact ih ha (.seq (isSimple_branch b simple) hi) ht h
        · contradiction
      | some value =>
        rcases value with ⟨cmp,lhs,rhs,x,y⟩
        have eq := (dest_If_thm _ cmp lhs rhs x y).mp hd
        subst b
        obtain ⟨hx,hy⟩ := tailEntry_ite_inv cmp lhs rhs x y hb
        simp only [hd] at h
        split at h
        · contradiction
        · split at h
          · contradiction
          · cases h
            exact .seq ha (.branch (constFp_branch (.ite cmp lhs rhs (.seq (.seq hx hi) ht) (.seq (.seq hy hi) ht))))

theorem tryIfHoist1_tailEntry {a b out : WordLangProgHOL (BitVec width)}
    (ha : WordTailEntryShape a) (hb : WordTailEntryShape b)
    (h : tryIfHoist1 a b = some out) : WordTailEntryShape out := by
  unfold tryIfHoist1 at h
  cases hd : destIf b with
  | none => simp [hd] at h
  | some value =>
    rcases value with ⟨cmp,lhs,rhs,x,y⟩
    have eq := (dest_If_thm _ cmp lhs rhs x y).mp hd
    subst b
    have parts := tailEntry_ite_inv cmp lhs rhs x y hb
    simp only [hd] at h
    exact tryIfHoist2_tailEntry _ ha .skip (.ite cmp lhs rhs parts.1 parts.2) h

theorem simpDuplicateIf_tailEntry {p : WordLangProgHOL (BitVec width)} (hp : WordTailEntryShape p) :
    WordTailEntryShape (simpDuplicateIf p) := by
  induction hp with
  | branch hp => exact .branch (simpDuplicateIf_branch hp)
  | call loc => exact .call loc
  | @seq a b ha hb iha ihb =>
    simp only [simpDuplicateIf]
    cases h : tryIfHoist1 (simpDuplicateIf a) (simpDuplicateIf b) with
    | none => exact .seq iha ihb
    | some out => exact seqAssoc_tailEntry (tryIfHoist1_tailEntry iha ihb h) (.branch .skip)

theorem pushOutIfAux_tailEntry {p : WordLangProgHOL (BitVec width)} (hp : WordTailEntryShape p) :
    WordTailEntryShape (pushOutIfAux p).1 := by
  induction hp with
  | branch hp => exact .branch (pushOutIfAux_branch hp)
  | call loc => exact .call loc
  | @seq a b ha hb iha ihb =>
    simp only [pushOutIfAux]
    rcases h : pushOutIfAux a with ⟨a',ba⟩
    simp only [h] at iha
    cases ba with
    | true => exact .seq iha hb
    | false =>
      rcases k : pushOutIfAux b with ⟨b',bb⟩
      simp only [k] at ihb
      exact .seq iha ihb

/-- Every stage of the actual WordSimp pass retains the entry shape. -/
theorem compileExp_tailEntry {p : WordLangProgHOL (BitVec width)} (hp : WordTailEntryShape p) :
    WordTailEntryShape (compileExp p) := by
  apply pushOutIfAux_tailEntry
  apply simpDuplicateIf_tailEntry
  apply constFpLoop_tailEntry
  exact seqAssoc_tailEntry hp (.branch .skip)

/-- The actual WordSimp output preserves evaluation and the tail-entry shape. -/
theorem compileExp_tailEntry_correct {C F : Type} {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s : WordSemStateFiniteExact width C F) (gc : gcFunConstOk s.gcFun) :
    WordTailEntryShape (compileExp p) ∧ evaluate (compileExp p) s = evaluate p s := by
  refine ⟨compileExp_tailEntry shape,?_⟩
  simp only [Compiler.Backend.WordSimp.compileExp]
  rw [evaluate_simp_push_out_if, evaluate_simp_duplicate_if _ _ gc,
    evaluate_const_fp _ _ gc, evaluate_Seq_assoc]

end SteppedFlapjack.WordSimpSteps
