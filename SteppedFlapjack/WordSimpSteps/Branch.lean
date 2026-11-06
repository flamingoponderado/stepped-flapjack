import SteppedFlapjack.WordSimpSteps.Loop

/-! Loop-free Word branches through the sequence normalizer. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

/-- Word branches with expressions and control exits, but no calls or loops. -/
inductive Branch : WordLangProgHOL (BitVec width) → Prop
  | assign (dst e) : Branch (.assign dst e)
  | inst (i) : Branch (.inst i)
  | move (pri ms) : Branch (.move pri ms)
  | get (dst name) : Branch (.get dst name)
  | set (name e) : Branch (.set name e)
  | store (e src) : Branch (.store e src)
  | skip : Branch .skip
  | tick : Branch .tick
  | ret (r vs) : Branch (.return r vs)
  | «break» (n) : Branch (.break n)
  | «continue» (n) : Branch (.continue n)
  | seq {a b} : Branch a → Branch b → Branch (.seq a b)
  | ite (cmp r ri) {a b} : Branch a → Branch b → Branch (.ite cmp r ri a b)

/-- A loop-free branch visits at most its syntax size. -/
theorem branch_static {p : WordLangProgHOL (BitVec width)} (hp : Branch p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ sizeOf p := by
  induction hp generalizing s with
  | seq ha hb iha ihb =>
    rw [steps_seq]
    have first := iha s
    rcases evaluate _ s with ⟨res,t⟩
    cases res with
    | none => have second := ihb t; simp_wf; omega
    | some r => simp_wf; omega
  | ite cmp r ri ha hb iha ihb =>
    rw [steps_ite]
    have first := iha s
    have second := ihb s
    cases getVar r s <;> cases getVarImm ri s <;> simp only
    all_goals try { simp_wf; omega }
    split <;> simp_wf <;> omega
  | assign _ _ | inst _ | move _ _ | get _ _ | set _ _ | store _ _ | skip | tick | ret _ _ | «break» _ | «continue» _ =>
    rw [steps_leaf _ _ rfl]
    simp_wf
    all_goals omega

/-- Smart sequencing retains the loop-free fragment. -/
theorem smartSeq_branch {a b : WordLangProgHOL (BitVec width)}
    (ha : Branch a) (hb : Branch b) : Branch (Compiler.Backend.WordSimp.smartSeqHOL a b) := by
  cases ha with
  | skip => exact hb
  | assign x e => exact .seq (.assign x e) hb
  | inst i => exact .seq (.inst i) hb
  | move pri ms => exact .seq (.move pri ms) hb
  | get x n => exact .seq (.get x n) hb
  | set n e => exact .seq (.set n e) hb
  | store e x => exact .seq (.store e x) hb
  | tick => exact .seq .tick hb
  | ret r vs => exact .seq (.ret r vs) hb
  | «break» n => exact .seq (.break n) hb
  | «continue» n => exact .seq (.continue n) hb
  | seq ha hc => exact .seq (.seq ha hc) hb
  | ite cmp r ri ha hc => exact .seq (.ite cmp r ri ha hc) hb

/-- Actual sequence normalization preserves loop-free branches. -/
theorem seqAssoc_branch {b : WordLangProgHOL (BitVec width)} (hb : Branch b) :
    ∀ {a : WordLangProgHOL (BitVec width)}, Branch a → Branch (seqAssoc a b) := by
  induction hb with
  | skip => intro a ha; simpa [Compiler.Backend.WordSimp.seqAssoc] using ha
  | seq hb hc ihb ihc => intro a ha; simp only [Compiler.Backend.WordSimp.seqAssoc]; exact ihc (ihb ha)
  | ite cmp r ri hb hc ihb ihc =>
    intro a ha
    simp only [Compiler.Backend.WordSimp.seqAssoc]
    exact smartSeq_branch ha (.ite cmp r ri (ihb .skip) (ihc .skip))
  | assign x e => intro a ha; exact smartSeq_branch ha (.assign x e)
  | inst i => intro a ha; exact smartSeq_branch ha (.inst i)
  | move pri ms => intro a ha; exact smartSeq_branch ha (.move pri ms)
  | get x n => intro a ha; exact smartSeq_branch ha (.get x n)
  | set n e => intro a ha; exact smartSeq_branch ha (.set n e)
  | store e x => intro a ha; exact smartSeq_branch ha (.store e x)
  | tick => intro a ha; exact smartSeq_branch ha .tick
  | ret r vs => intro a ha; exact smartSeq_branch ha (.ret r vs)
  | «break» n => intro a ha; exact smartSeq_branch ha (.break n)
  | «continue» n => intro a ha; exact smartSeq_branch ha (.continue n)

/-- Sequence normalization preserves evaluation and bounds branch visits. -/
theorem seqAssoc_branch_correct {p : WordLangProgHOL (BitVec width)} (hp : Branch p)
    (s : WordSemStateFiniteExact width C F) :
    evaluate (seqAssoc .skip p) s = evaluate p s ∧
    steps (seqAssoc .skip p) s ≤ sizeOf (seqAssoc .skip p) * steps p s := by
  refine ⟨evaluate_Seq_assoc p s, ?_⟩
  have h := branch_static (seqAssoc_branch hp .skip) s
  have positive := steps_pos p s
  nlinarith

/-- The same normalization bound holds for a loop with a branching body. -/
theorem seqAssoc_loop_branch (names exits : Spt Unit)
    {body : WordLangProgHOL (BitVec width)} (shape : Branch body)
    (source : WordSemStateFiniteExact width C F) :
    evaluate (seqAssoc .skip (.loop names body exits)) source = evaluate (.loop names body exits) source ∧
    steps (seqAssoc .skip (.loop names body exits)) source ≤
      (1 + sizeOf (seqAssoc .skip body)) * steps (.loop names body exits) source := by
  refine ⟨evaluate_Seq_assoc _ source, ?_⟩
  change steps (.loop names (seqAssoc .skip body) exits) source ≤ _
  exact loop_body_steps_bound names exits body (seqAssoc .skip body) _
    (fun s => evaluate_Seq_assoc body s) (fun s => (seqAssoc_branch_correct shape s).2) source

end SteppedFlapjack.WordSimpSteps
