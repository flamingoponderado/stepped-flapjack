import SteppedFlapjack.WordSimpSteps.TailCallBound

/-! WordSimp preserves the set of allowed direct tail-call destinations. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp
open SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width] {allowed : Nat → Prop}

/-- Branches and tail calls whose destination satisfies a fixed predicate. -/
inductive AllowedTailEntry (allowed : Nat → Prop) : WordLangProgHOL (BitVec width) → Prop
  | branch {p} : Branch p → AllowedTailEntry allowed p
  | call (loc) : allowed loc → AllowedTailEntry allowed (.call none (some loc) [0] none)
  | seq {a b} : AllowedTailEntry allowed a → AllowedTailEntry allowed b → AllowedTailEntry allowed (.seq a b)

theorem smartSeq_allowedTailEntry {a b : WordLangProgHOL (BitVec width)}
    (ha : AllowedTailEntry allowed a) (hb : AllowedTailEntry allowed b) :
    AllowedTailEntry allowed (Compiler.Backend.WordSimp.smartSeqHOL a b) := by
  cases a <;> simp only [Compiler.Backend.WordSimp.smartSeqHOL] <;> first | exact hb | exact .seq ha hb

/-- Sequence reassociation keeps the direct call and all branch prefixes. -/
theorem seqAssoc_allowedTailEntry {p : WordLangProgHOL (BitVec width)} (hp : AllowedTailEntry allowed p) :
    ∀ {prelude}, AllowedTailEntry allowed prelude → AllowedTailEntry allowed (Compiler.Backend.WordSimp.seqAssoc prelude p) := by
  induction hp with
  | branch hp =>
    intro prelude pre
    induction hp generalizing prelude with
    | skip => simpa only [Compiler.Backend.WordSimp.seqAssoc] using pre
    | seq ha hb iha ihb => simp only [Compiler.Backend.WordSimp.seqAssoc]; exact ihb (iha pre)
    | ite cmp r ri ha hb iha ihb =>
      simp only [Compiler.Backend.WordSimp.seqAssoc]
      exact smartSeq_allowedTailEntry pre (.branch (.ite cmp r ri (seqAssoc_branch ha .skip) (seqAssoc_branch hb .skip)))
    | assign dst e => exact smartSeq_allowedTailEntry pre (.branch (.assign dst e))
    | inst i => exact smartSeq_allowedTailEntry pre (.branch (.inst i))
    | move pri ms => exact smartSeq_allowedTailEntry pre (.branch (.move pri ms))
    | get dst n => exact smartSeq_allowedTailEntry pre (.branch (.get dst n))
    | opCurrHeap op dst src => exact smartSeq_allowedTailEntry pre (.branch (.opCurrHeap op dst src))
    | set n e => exact smartSeq_allowedTailEntry pre (.branch (.set n e))
    | store e src => exact smartSeq_allowedTailEntry pre (.branch (.store e src))
    | tick => exact smartSeq_allowedTailEntry pre (.branch .tick)
    | ret r vs => exact smartSeq_allowedTailEntry pre (.branch (.ret r vs))
    | «break» n => exact smartSeq_allowedTailEntry pre (.branch (.break n))
    | «continue» n => exact smartSeq_allowedTailEntry pre (.branch (.continue n))
  | call loc good => intro prelude pre; exact smartSeq_allowedTailEntry pre (.call loc good)
  | seq ha hb iha ihb => intro prelude pre; simp only [Compiler.Backend.WordSimp.seqAssoc]; exact ihb (iha pre)

/-- Materializing constant arguments produces only supported branch code. -/
theorem dropConsts_branch_allowed (cs : Spt (BitVec width)) (args : List Nat) : Branch (dropConsts cs args) := by
  induction args with
  | nil => exact .skip
  | cons n ns ih =>
    simp only [dropConsts]
    cases h : sptLookup n cs with
    | none => simpa only [h] using ih
    | some w => simpa only [h] using smartSeq_branch ih (.assign n (.const w))

/-- Constant propagation may materialize the return-location argument, while
preserving the direct call and supported branch shape. -/
theorem constFpLoop_allowedTailEntry {p : WordLangProgHOL (BitVec width)} (hp : AllowedTailEntry allowed p) :
    ∀ cs, AllowedTailEntry allowed (constFpLoop p cs).1 := by
  induction hp with
  | branch hp => intro cs; exact .branch (constFpLoop_branch hp cs)
  | call loc good => intro cs; exact smartSeq_allowedTailEntry (.branch (dropConsts_branch_allowed cs [0])) (.call loc good)
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
theorem allowedTailEntry_ite_inv (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (h : AllowedTailEntry allowed (.ite cmp r ri a b)) : Branch a ∧ Branch b := by
  cases h with
  | branch h => cases h with | ite _ _ _ ha hb => exact ⟨ha,hb⟩

theorem tryIfHoist2_allowedTailEntry (fuel : Nat) : ∀
    {p interm dummy after out : WordLangProgHOL (BitVec width)},
    AllowedTailEntry allowed p → Branch interm → Branch after →
    tryIfHoist2 fuel p interm dummy after = some out → AllowedTailEntry allowed out := by
  induction fuel with
  | zero => intros; simp_all [tryIfHoist2]
  | succ fuel ih =>
    intro p interm dummy after out hp hi ht h
    cases hp with
    | branch hp => exact .branch (tryIfHoist2_branch _ hp hi ht h)
    | call loc good => simp [tryIfHoist2] at h
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
        obtain ⟨hx,hy⟩ := allowedTailEntry_ite_inv cmp lhs rhs x y hb
        simp only [hd] at h
        split at h
        · contradiction
        · split at h
          · contradiction
          · cases h
            exact .seq ha (.branch (constFp_branch (.ite cmp lhs rhs (.seq (.seq hx hi) ht) (.seq (.seq hy hi) ht))))

theorem tryIfHoist1_allowedTailEntry {a b out : WordLangProgHOL (BitVec width)}
    (ha : AllowedTailEntry allowed a) (hb : AllowedTailEntry allowed b)
    (h : tryIfHoist1 a b = some out) : AllowedTailEntry allowed out := by
  unfold tryIfHoist1 at h
  cases hd : destIf b with
  | none => simp [hd] at h
  | some value =>
    rcases value with ⟨cmp,lhs,rhs,x,y⟩
    have eq := (dest_If_thm _ cmp lhs rhs x y).mp hd
    subst b
    have parts := allowedTailEntry_ite_inv cmp lhs rhs x y hb
    simp only [hd] at h
    exact tryIfHoist2_allowedTailEntry _ ha .skip (.ite cmp lhs rhs parts.1 parts.2) h

theorem simpDuplicateIf_allowedTailEntry {p : WordLangProgHOL (BitVec width)} (hp : AllowedTailEntry allowed p) :
    AllowedTailEntry allowed (simpDuplicateIf p) := by
  induction hp with
  | branch hp => exact .branch (simpDuplicateIf_branch hp)
  | call loc good => exact .call loc good
  | @seq a b ha hb iha ihb =>
    simp only [simpDuplicateIf]
    cases h : tryIfHoist1 (simpDuplicateIf a) (simpDuplicateIf b) with
    | none => exact .seq iha ihb
    | some out => exact seqAssoc_allowedTailEntry (tryIfHoist1_allowedTailEntry iha ihb h) (.branch .skip)

theorem pushOutIfAux_allowedTailEntry {p : WordLangProgHOL (BitVec width)} (hp : AllowedTailEntry allowed p) :
    AllowedTailEntry allowed (pushOutIfAux p).1 := by
  induction hp with
  | branch hp => exact .branch (pushOutIfAux_branch hp)
  | call loc good => exact .call loc good
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
theorem compileExp_allowedTailEntry {p : WordLangProgHOL (BitVec width)} (hp : AllowedTailEntry allowed p) :
    AllowedTailEntry allowed (compileExp p) := by
  apply pushOutIfAux_allowedTailEntry
  apply simpDuplicateIf_allowedTailEntry
  apply constFpLoop_allowedTailEntry
  exact seqAssoc_allowedTailEntry hp (.branch .skip)


omit [NeZero width] in
/-- A code bound gives an allowed-destination witness for the original entry. -/
theorem tailEntry_allowed_of_code {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat)
    (bound : TailEntryCodeBound p code K) :
    AllowedTailEntry (fun loc => ∃ callee, sptLookup loc code = some (1,callee) ∧
      LoopSequence callee ∧ sizeOf callee ≤ K) p := by
  induction shape with
  | branch h => exact .branch h
  | call loc => exact .call loc (bound loc (.call loc))
  | @seq a b ha hb iha ihb =>
    exact .seq (iha (fun loc h => bound loc (.left h))) (ihb (fun loc h => bound loc (.right h)))

omit [NeZero width] in
/-- Every direct call in an allowed entry satisfies its destination predicate. -/
theorem allowedTailEntry_calls {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) : ∀ loc, TailEntryCalls p loc → allowed loc := by
  induction shape with
  | branch h =>
    intro loc call
    induction h <;> cases call <;> simp_all
  | call loc good => intro target call; cases call; exact good
  | seq ha hb iha ihb =>
    intro loc call
    cases call with
    | left h => exact iha loc h
    | right h => exact ihb loc h

/-- WordSimp introduces no destination lacking the input's proved code bound. -/
theorem compileExp_tailEntry_codeBound {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat)
    (bound : TailEntryCodeBound p code K) : TailEntryCodeBound (compileExp p) code K := by
  have h := compileExp_allowedTailEntry (tailEntry_allowed_of_code shape code K bound)
  exact allowedTailEntry_calls h

/-- WordSimp preserves a normalized tail-entry execution with a visit bound;
the output's callee obligations follow from those of the original entry. -/
theorem tailEntry_wordSimp_normalized_derived {C F : Type} {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K limit : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : WordSteps.steps p s ≤ limit) (gc : gcFunConstOk s.gcFun) :
    evaluate (compileExp p) {s with clock := limit} =
        (res,{post with clock := limit-(s.clock-post.clock)}) ∧
    WordSteps.steps (compileExp p) {s with clock := limit} ≤
      sizeOf (compileExp p) * (K+1) * (limit+1) :=
  tailEntry_wordSimp_normalized shape s post res K limit noInstallCode code
    (compileExp_tailEntry_codeBound shape s.code K code) run notError notTimeout sourceBound gc

/-- Loop-to-Word compilation retains the single destination of a Loop entry. -/
theorem singleTail_word_allowed {loc : Nat} {p : HolLoopProg width}
    (shape : SingleTailEntryShape loc p) (ctxt : Spt Nat) :
    ∀ labels, AllowedTailEntry (fun dest => dest = loc) (LoopToWord.compHOL ctxt p labels).1 := by
  induction shape with
  | branch h => intro labels; exact .branch (LoopToWordSteps.loopBranch_word h ctxt labels)
  | call => intro labels; cases labels; simp only [LoopToWord.compHOL,List.map_nil]; exact .call loc rfl
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL]
    exact .seq (iha labels) (ihb (LoopToWord.compHOL ctxt a labels).2)
  | mark h ih => intro labels; simpa only [LoopToWord.compHOL] using ih labels

/-- The actual compiler code relation supplies the sole Word callee and its
supported shape and size for a single-destination Loop entry. -/
theorem singleTail_word_codeBound {loc : Nat} {p callee : HolLoopProg width}
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopToWordSteps.LoopSequenceSource callee)
    (loopCode : Spt (List Nat × HolLoopProg width))
    (wordCode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (codeRel : loopToWordCodeRelHOLExact loopCode wordCode)
    (lookup : sptLookup loc loopCode = some ([],callee)) (ctxt : Spt Nat) (labels : Nat × Nat) :
    TailEntryCodeBound (LoopToWord.compHOL ctxt p labels).1 wordCode
      (sizeOf (loopToWordCompFuncHOL loc [] callee)) := by
  have allowed := singleTail_word_allowed shape ctxt labels
  intro dest call
  have eq : dest = loc := allowedTailEntry_calls allowed dest call
  subst dest
  refine ⟨loopToWordCompFuncHOL loc [] callee,?_,?_,le_rfl⟩
  · simpa using (codeRel loc [] callee lookup).1
  · unfold loopToWordCompFuncHOL
    exact LoopToWordSteps.loopSequenceSource_word calleeShape _ _

end SteppedFlapjack.WordSimpSteps
