import SteppedFlapjack.Concrete.SimpRun
import SteppedFlapjack.CrepSteps.BranchStatic

/-! pan_simp (seqAssoc) overhead charged to the SIMPLIFIED body weight. -/
namespace SteppedFlapjack.Concrete.SimpVisits
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.Concrete

variable {width : Nat} [NeZero width] {σ : Type}

def hw : ProgHOL width → Nat
  | .dec _ _ _ body => 1 + hw body
  | .seq a b => 1 + hw a + hw b
  | .ite _ a b => 1 + hw a + hw b
  | .while _ body => 1 + hw body
  | _ => 1

/-- HOL images of call-free, loop-exit-free bodies. -/
private inductive Plain : ProgHOL width → Prop
  | skip : Plain .skip
  | assign (k n e) : Plain (.assign k n e)
  | ret (e) : Plain (.return e)
  | dec (n sh e) {body} : Plain body → Plain (.dec n sh e body)
  | seq {a b} : Plain a → Plain b → Plain (.seq a b)
  | ite (e) {a b} : Plain a → Plain b → Plain (.ite e a b)
  | while (e) {body} : Plain body → Plain (.while e body)

private def isSkip : ProgHOL width → Bool
  | .skip => true
  | _ => false

private noncomputable def prePart (pre : ProgHOL width) (s : PanSemStateFiniteExact width σ) : Nat :=
  if isSkip pre then 0 else 1 + controlSteps pre s

private noncomputable def after (pre p : ProgHOL width) (s : PanSemStateFiniteExact width σ) : Nat :=
  match s.evaluateHOLFiniteState pre with
  | (none,t) => controlSteps p t
  | _ => 0

def exitOver (r : Option (PanSemResultExact width)) (w : Nat) : Nat :=
  match r with
  | none => 0
  | some _ => w

private theorem over_le (r : Option (PanSemResultExact width)) (w : Nat) : exitOver r w ≤ w := by
  cases r <;> simp [exitOver]

private def NoExit (r : Option (PanSemResultExact width)) : Prop := r ≠ some .break ∧ r ≠ some .continue

/-- Plain bodies never produce a loop exit. -/
private theorem plain_no_loop_exit {p : ProgHOL width} (plain : Plain p) :
    ∀ (s : PanSemStateFiniteExact width σ),
      (s.evaluateHOLFiniteState p).1 ≠ some .break ∧ (s.evaluateHOLFiniteState p).1 ≠ some .continue := by
  induction plain with
  | skip => intro s; simp
  | assign k n e =>
    intro s
    rw [evaluateHOLFiniteState_assign]
    repeat' (first | split | simp)
  | ret e =>
    intro s
    rw [evaluateHOLFiniteState_return]
    repeat' (first | split | simp)
  | @dec n sh e body _ ih =>
    intro s
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    cases h : @evalHOLExact width σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
    | none => simp
    | some v =>
      by_cases valid : shapeEqHOL sh (shapeOfHOLExact v) = true
      · simpa [valid] using ih (setVarHOLFinite n v s)
      · simp [valid]
  | @seq a b _ _ iha ihb =>
    intro s
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := iha s
    rcases run : s.evaluateHOLFiniteState a with ⟨r,t⟩
    rw [run] at ha
    cases r with
    | none => simpa using ihb t
    | some x => simpa using ha
  | @ite e a b _ _ iha ihb =>
    intro s
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact ihb s
      · exact iha s
    · simp
  | @«while» e body _ ih =>
    intro s
    induction hc : s.clock using Nat.strongRecOn generalizing s with
    | _ clock ihc =>
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      split
      · rename_i word _
        by_cases zero : word = 0
        · simp [zero]
        · by_cases noClock : s.clock = 0
          · simp [show ¬ word = 0#width from zero, noClock]
          · rw [if_pos zero, if_neg noClock]
            have hb := ih s.decClockHOLFinite
            rcases run : s.decClockHOLFinite.evaluateHOLFiniteState body with ⟨r,u⟩
            rw [run] at hb
            have mono := evaluateHOLFiniteState_clock_le s.decClockHOLFinite body
            rw [run] at mono
            have smaller : u.clock < clock := by simp only [decClockHOLFinite] at mono; omega
            cases r with
            | none => simpa using ihc u.clock smaller u rfl
            | some x =>
              cases x with
              | «break» => exact absurd rfl hb.1
              | «continue» => exact absurd rfl hb.2
              | error | timeOut | returned _ | finalFfi _ | exception _ _ => simp
      · simp

private theorem eval_seqAssoc_skip (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) :
    s.evaluateHOLFiniteState (seqAssocHOL .skip p) = s.evaluateHOLFiniteState p := by
  rw [evaluateSeqAssocHOL,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip]


private theorem exitOver_mono (r : Option (PanSemResultExact width)) {w v : Nat} (h : w ≤ v) :
    exitOver r w ≤ exitOver r v := by
  cases r <;> simp [exitOver, h]

private theorem controlSteps_skip (s : PanSemStateFiniteExact width σ) : controlSteps (.skip : ProgHOL width) s = 1 := by
  rw [controlSteps.eq_def]; rfl

/-- Declarations: the node bound follows from the body bound. -/
private theorem dec_node (n : MlS) (sh : ShapeHOL) (e : ExpHOL width) (body body' : ProgHOL width) (w : Nat)
    (hb : ∀ t : PanSemStateFiniteExact width σ,
      controlSteps body' t ≤ controlSteps body t + exitOver (t.evaluateHOLFiniteState body).1 w)
    (t : PanSemStateFiniteExact width σ) :
    controlSteps (.dec n sh e body') t ≤ controlSteps (.dec n sh e body) t +
      exitOver (t.evaluateHOLFiniteState (.dec n sh e body)).1 w := by
  cases h : @evalHOLExact width σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e with
  | none =>
    rw [controlSteps.eq_def, controlSteps.eq_def (.dec n sh e body)]
    simp [h]
  | some v =>
    by_cases valid : shapeEqHOL sh (shapeOfHOLExact v) = true
    · rw [controlSteps_dec n sh e body' t v h valid, controlSteps_dec n sh e body t v h valid,
        evaluateHOLFiniteState_dec_total]
      simp only [h, valid, if_true]
      have := hb (PanSemStateFiniteExact.setVarHOLFinite n v t)
      omega
    · rw [controlSteps.eq_def, controlSteps.eq_def (.dec n sh e body)]
      simp [h, valid]

/-- Conditionals: the node bound follows from both branch bounds. -/
private theorem ite_node (e : ExpHOL width) (a a' b b' : ProgHOL width) (w : Nat)
    (ha : ∀ t : PanSemStateFiniteExact width σ,
      controlSteps a' t ≤ controlSteps a t + exitOver (t.evaluateHOLFiniteState a).1 w)
    (hb : ∀ t : PanSemStateFiniteExact width σ,
      controlSteps b' t ≤ controlSteps b t + exitOver (t.evaluateHOLFiniteState b).1 w)
    (t : PanSemStateFiniteExact width σ) :
    controlSteps (.ite e a' b') t ≤ controlSteps (.ite e a b) t +
      exitOver (t.evaluateHOLFiniteState (.ite e a b)).1 w := by
  rw [controlSteps_ite, controlSteps_ite, evaluateHOLFiniteState_ite]
  cases h : @evalHOLExact width σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e with
  | none => simp [exitOver]
  | some v =>
    rcases v with ⟨⟨word⟩⟩ | _ | _ <;> simp only [exitOver] <;> try omega
    by_cases zero : word = 0
    · have := hb t; simp only [exitOver] at this; simp [zero]; omega
    · have := ha t; simp only [exitOver] at this; simp [show ¬ word = 0#width from zero]; omega

/-- Loops: a normal iteration costs no extra visits; the bound is charged
only once, on the abnormal exit. -/
private theorem while_node (e : ExpHOL width) (body body' : ProgHOL width) (w : Nat)
    (hb : ∀ t : PanSemStateFiniteExact width σ,
      controlSteps body' t ≤ controlSteps body t + exitOver (t.evaluateHOLFiniteState body).1 w)
    (heval : ∀ t : PanSemStateFiniteExact width σ, t.evaluateHOLFiniteState body' = t.evaluateHOLFiniteState body)
    (noexit : ∀ t : PanSemStateFiniteExact width σ,
      (t.evaluateHOLFiniteState body).1 ≠ some .break ∧ (t.evaluateHOLFiniteState body).1 ≠ some .continue)
    (t : PanSemStateFiniteExact width σ) :
    controlSteps (.while e body') t ≤ controlSteps (.while e body) t +
      exitOver (t.evaluateHOLFiniteState (.while e body)).1 w := by
  induction hc : t.clock using Nat.strongRecOn generalizing t with
  | _ clock ih =>
    rw [controlSteps_while, controlSteps_while, evaluateHOLFiniteState_while_fixClockRewrite]
    have hf : @evalHOLFinite width σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) e =
        @evalHOLExact width σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e := rfl
    rw [hf]
    cases h : @evalHOLExact width σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e with
    | none => simp
    | some v =>
      rcases v with ⟨⟨word⟩⟩ | _ | _ <;> simp only <;> try omega
      by_cases zero : word = 0
      · simp [zero]
      · by_cases noClock : t.clock = 0
        · simp [noClock]
        · simp only [ne_eq, zero, not_false_eq_true, noClock, and_self, if_true, if_false]
          rw [heval]
          have bodyCost := hb t.decClockHOLFinite
          have exits := noexit t.decClockHOLFinite
          rcases run : t.decClockHOLFinite.evaluateHOLFiniteState body with ⟨r,u⟩
          rw [run] at bodyCost exits
          have mono := evaluateHOLFiniteState_clock_le t.decClockHOLFinite body
          rw [run] at mono
          have smaller : u.clock < clock := by
            simp only [decClockHOLFinite] at mono; omega
          cases r with
          | none =>
            have rest := ih u.clock smaller u rfl
            simp only [exitOver] at bodyCost rest ⊢
            omega
          | some r =>
            cases r with
            | «break» => exact absurd rfl exits.1
            | «continue» => exact absurd rfl exits.2
            | error | timeOut | returned _ | finalFfi _ | exception _ _ =>
              simp only [exitOver] at bodyCost ⊢
              omega

/-- Lift a per-node bound through the `smartSeqHOL` accumulator. -/
private theorem smart_bound (pre x x' : ProgHOL width) (w : Nat)
    (node : ∀ t : PanSemStateFiniteExact width σ,
      controlSteps x' t ≤ controlSteps x t + exitOver (t.evaluateHOLFiniteState x).1 w)
    (s : PanSemStateFiniteExact width σ) :
    controlSteps (smartSeqHOL pre x') s ≤
      prePart pre s + after pre x s + exitOver (s.evaluateHOLFiniteState (.seq pre x)).1 w := by
  cases hpre : isSkip pre with
  | true =>
    have : pre = .skip := by cases pre <;> simp_all [isSkip]
    subst this
    simpa [smartSeqHOL,prePart,isSkip,after,evaluateHOLFiniteState_seq_line780] using node s
  | false =>
    have smart : smartSeqHOL pre x' = .seq pre x' := by cases pre <;> simp_all [isSkip,smartSeqHOL]
    rw [smart,controlSteps_seq]
    simp only [prePart,hpre,Bool.false_eq_true,if_false,after,evaluateHOLFiniteState_seq_line780]
    rcases run : s.evaluateHOLFiniteState pre with ⟨r,t⟩
    cases r with
    | none => have := node t; simp only; omega
    | some r => simp only; omega

private theorem smart_eq_skip {pre x : ProgHOL width} (h : smartSeqHOL pre x = .skip) : x = .skip := by
  unfold smartSeqHOL at h
  split at h
  · exact h
  · cases h

private theorem seqAssoc_eq_skip {a : ProgHOL width} (plain : Plain a) :
    ∀ pre : ProgHOL width, seqAssocHOL pre a = .skip → pre = .skip := by
  induction plain with
  | skip => intro pre h; simpa [seqAssocHOL] using h
  | assign k n e =>
    intro pre h
    rw [show seqAssocHOL pre (.assign k n e : ProgHOL width) = smartSeqHOL pre (.assign k n e) by simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | ret e =>
    intro pre h
    rw [show seqAssocHOL pre (.return e : ProgHOL width) = smartSeqHOL pre (.return e) by simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | @dec n sh e body _ _ =>
    intro pre h
    rw [show seqAssocHOL pre (.dec n sh e body) = smartSeqHOL pre (.dec n sh e (seqAssocHOL .skip body)) by
      simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | seq _ _ iha ihb => intro pre h; rw [seqAssocHOL] at h; exact iha pre (ihb _ h)
  | @ite e a b _ _ _ _ =>
    intro pre h
    rw [show seqAssocHOL pre (.ite e a b) =
      smartSeqHOL pre (.ite e (seqAssocHOL .skip a) (seqAssocHOL .skip b)) by simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | @«while» e body _ _ =>
    intro pre h
    rw [show seqAssocHOL pre (.while e body) = smartSeqHOL pre (.while e (seqAssocHOL .skip body)) by
      simp [seqAssocHOL]] at h
    cases smart_eq_skip h

private theorem eval_seq_skip (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) :
    s.evaluateHOLFiniteState (.seq .skip p) = s.evaluateHOLFiniteState p := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]


private def hwPre (pre : ProgHOL width) : Nat := if isSkip pre then 0 else hw pre

/-- Weight that the simplified output adds on top of the accumulator. -/
private def delta (pre p : ProgHOL width) : Nat := hw (seqAssocHOL pre p) - hwPre pre

private theorem isSkip_false_ne {pre : ProgHOL width} (h : isSkip pre = false) : pre ≠ .skip := by
  rintro rfl; simp [isSkip] at h

private theorem smart_hw (pre x : ProgHOL width) :
    hw (smartSeqHOL pre x) = hwPre pre + hw x + (if isSkip pre then 0 else 1) := by
  cases h : isSkip pre
  · have smart : smartSeqHOL pre x = .seq pre x := by cases pre <;> simp_all [isSkip,smartSeqHOL]
    simp [smart,hw,hwPre,h]; omega
  · have : pre = .skip := by cases pre <;> simp_all [isSkip]
    subst this; simp [smartSeqHOL,hwPre,isSkip]

private theorem seqAssoc_dec (pre : ProgHOL width) (n sh e body) :
    seqAssocHOL pre (.dec n sh e body) = smartSeqHOL pre (.dec n sh e (seqAssocHOL .skip body)) := by
  simp [seqAssocHOL]
private theorem seqAssoc_ite (pre : ProgHOL width) (e a b) :
    seqAssocHOL pre (.ite e a b) = smartSeqHOL pre (.ite e (seqAssocHOL .skip a) (seqAssocHOL .skip b)) := by
  simp [seqAssocHOL]
private theorem seqAssoc_while (pre : ProgHOL width) (e body) :
    seqAssocHOL pre (.while e body) = smartSeqHOL pre (.while e (seqAssocHOL .skip body)) := by
  simp [seqAssocHOL]
private theorem seqAssoc_assign (pre : ProgHOL width) (k n e) :
    seqAssocHOL pre (.assign k n e) = smartSeqHOL pre (.assign k n e) := by simp [seqAssocHOL]
private theorem seqAssoc_ret (pre : ProgHOL width) (e) :
    seqAssocHOL pre (.return e) = smartSeqHOL pre (.return e) := by simp [seqAssocHOL]

/-- The accumulator survives in the output. -/
private theorem hwPre_le {p : ProgHOL width} (plain : Plain p) :
    ∀ pre : ProgHOL width, hwPre pre ≤ hw (seqAssocHOL pre p) := by
  induction plain with
  | skip => intro pre; simp only [show seqAssocHOL pre (.skip : ProgHOL width) = pre by simp [seqAssocHOL], hwPre]; split <;> omega
  | assign k n e => intro pre; rw [seqAssoc_assign, smart_hw]; omega
  | ret e => intro pre; rw [seqAssoc_ret, smart_hw]; omega
  | dec n sh e _ _ => intro pre; rw [seqAssoc_dec, smart_hw]; omega
  | ite e _ _ _ _ => intro pre; rw [seqAssoc_ite, smart_hw]; omega
  | «while» e _ _ => intro pre; rw [seqAssoc_while, smart_hw]; omega
  | @seq a b aPlain _ iha ihb =>
    intro pre
    rw [show seqAssocHOL pre (.seq a b) = seqAssocHOL (seqAssocHOL pre a) b by rw [seqAssocHOL]]
    have h1 := iha pre
    have h2 := ihb (seqAssocHOL pre a)
    cases hs : isSkip (seqAssocHOL pre a)
    · have : hwPre (seqAssocHOL pre a) = hw (seqAssocHOL pre a) := by simp [hwPre,hs]
      omega
    · have e1 : seqAssocHOL pre a = .skip := by cases h : seqAssocHOL pre a <;> simp_all [isSkip]
      have e2 := seqAssoc_eq_skip aPlain pre e1
      subst e2
      simp [hwPre,isSkip]

/-- Once the accumulator has exited abnormally, the output only adds the
sequence nodes counted by `delta`. -/
private theorem abnormal_visits {p : ProgHOL width} (plain : Plain p) :
    ∀ (pre : ProgHOL width) (s : PanSemStateFiniteExact width σ), isSkip pre = false →
      (s.evaluateHOLFiniteState pre).1 ≠ none →
      controlSteps (seqAssocHOL pre p) s ≤ controlSteps pre s + delta pre p := by
  have leaf : ∀ (pre x : ProgHOL width) (s : PanSemStateFiniteExact width σ), isSkip pre = false →
      (s.evaluateHOLFiniteState pre).1 ≠ none →
      controlSteps (smartSeqHOL pre x) s ≤ controlSteps pre s + (hw (smartSeqHOL pre x) - hwPre pre) := by
    intro pre x s hs ab
    have smart : smartSeqHOL pre x = .seq pre x := by cases pre <;> simp_all [isSkip,smartSeqHOL]
    rw [smart, controlSteps_seq]
    rcases run : s.evaluateHOLFiniteState pre with ⟨r,t⟩
    rw [run] at ab
    cases r with
    | none => exact absurd rfl ab
    | some x => simp [hw,hwPre,hs]; omega
  induction plain with
  | skip => intro pre s _ _; simp [show seqAssocHOL pre (.skip : ProgHOL width) = pre by simp [seqAssocHOL]]
  | assign k n e => intro pre s hs ab; unfold delta; rw [seqAssoc_assign]; exact leaf _ _ s hs ab
  | ret e => intro pre s hs ab; unfold delta; rw [seqAssoc_ret]; exact leaf _ _ s hs ab
  | dec n sh e _ _ => intro pre s hs ab; unfold delta; rw [seqAssoc_dec]; exact leaf _ _ s hs ab
  | ite e _ _ _ _ => intro pre s hs ab; unfold delta; rw [seqAssoc_ite]; exact leaf _ _ s hs ab
  | «while» e _ _ => intro pre s hs ab; unfold delta; rw [seqAssoc_while]; exact leaf _ _ s hs ab
  | @seq a b aPlain bPlain iha ihb =>
    intro pre s hs ab
    have split : seqAssocHOL pre (.seq a b) = seqAssocHOL (seqAssocHOL pre a) b := by rw [seqAssocHOL]
    unfold delta; rw [split]
    have hs' : isSkip (seqAssocHOL pre a) = false := by
      cases h : isSkip (seqAssocHOL pre a)
      · rfl
      · have e1 : seqAssocHOL pre a = .skip := by cases h' : seqAssocHOL pre a <;> simp_all [isSkip]
        have := seqAssoc_eq_skip aPlain pre e1
        subst this; simp [isSkip] at hs
    have ab' : (s.evaluateHOLFiniteState (seqAssocHOL pre a)).1 ≠ none := by
      rw [evaluateSeqAssocHOL, evaluateHOLFiniteState_seq_line780]
      rcases run : s.evaluateHOLFiniteState pre with ⟨r,t⟩
      rw [run] at ab
      cases r with
      | none => exact absurd rfl ab
      | some x => simp
    have h1 := iha pre s hs ab
    have h2 := ihb (seqAssocHOL pre a) s hs' ab'
    have m1 := hwPre_le aPlain pre
    have m2 := hwPre_le bPlain (seqAssocHOL pre a)
    unfold delta at h1 h2
    simp only [hwPre, hs, hs', Bool.false_eq_true, if_false] at h1 h2 m1 m2 ⊢
    omega

/-- Main accumulator bound, with the exit overhead charged to the output. -/
private theorem seqAssoc_visits_delta {p : ProgHOL width} (plain : Plain p) :
    ∀ (pre : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      controlSteps (seqAssocHOL pre p) s ≤
        prePart pre s + after pre p s + exitOver (s.evaluateHOLFiniteState (.seq pre p)).1 (delta pre p) := by
  have skipForm : ∀ {q : ProgHOL width}, (∀ (pre : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      controlSteps (seqAssocHOL pre q) s ≤
        prePart pre s + after pre q s + exitOver (s.evaluateHOLFiniteState (.seq pre q)).1 (delta pre q)) →
      ∀ t : PanSemStateFiniteExact width σ, controlSteps (seqAssocHOL .skip q) t ≤
        controlSteps q t + exitOver (t.evaluateHOLFiniteState q).1 (hw (seqAssocHOL .skip q)) := by
    intro q h t
    simpa [prePart, isSkip, after, eval_seq_skip, delta, hwPre] using h .skip t
  have smartDelta : ∀ (pre x : ProgHOL width), hw x ≤ hw (smartSeqHOL pre x) - hwPre pre := by
    intro pre x; rw [smart_hw]; omega
  induction plain with
  | skip =>
    intro pre s
    rw [show seqAssocHOL pre (.skip : ProgHOL width) = pre by simp [seqAssocHOL]]
    cases hpre : isSkip pre with
    | true =>
      have : pre = .skip := by cases pre <;> simp_all [isSkip]
      subst this
      simp [controlSteps_skip, after, prePart, isSkip]
    | false => simp [prePart, hpre]; omega
  | assign k n e =>
    intro pre s
    unfold delta; rw [seqAssoc_assign]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | ret e =>
    intro pre s
    unfold delta; rw [seqAssoc_ret]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | @dec n sh e body _ ih =>
    intro pre s
    unfold delta; rw [seqAssoc_dec]
    apply smart_bound
    intro t
    apply dec_node
    intro u
    refine (skipForm ih u).trans (Nat.add_le_add_left (exitOver_mono _ ?_) _)
    have := smartDelta pre (.dec n sh e (seqAssocHOL .skip body))
    simp only [hw] at this; omega
  | @ite e a b _ _ iha ihb =>
    intro pre s
    unfold delta; rw [seqAssoc_ite]
    apply smart_bound
    intro t
    have := smartDelta pre (.ite e (seqAssocHOL .skip a) (seqAssocHOL .skip b))
    simp only [hw] at this
    apply ite_node
    · intro u; exact (skipForm iha u).trans (Nat.add_le_add_left (exitOver_mono _ (by omega)) _)
    · intro u; exact (skipForm ihb u).trans (Nat.add_le_add_left (exitOver_mono _ (by omega)) _)
  | @«while» e body bodyPlain ih =>
    intro pre s
    unfold delta; rw [seqAssoc_while]
    apply smart_bound
    intro t
    have := smartDelta pre (.while e (seqAssocHOL .skip body))
    simp only [hw] at this
    apply while_node
    · intro u; exact (skipForm ih u).trans (Nat.add_le_add_left (exitOver_mono _ (by omega)) _)
    · intro u; exact eval_seqAssoc_skip body u
    · exact plain_no_loop_exit bodyPlain
  | @seq a b aPlain bPlain iha ihb =>
    intro pre s
    have split : seqAssocHOL pre (.seq a b) = seqAssocHOL (seqAssocHOL pre a) b := by rw [seqAssocHOL]
    have preEval : s.evaluateHOLFiniteState (seqAssocHOL pre a) = s.evaluateHOLFiniteState (.seq pre a) :=
      evaluateSeqAssocHOL pre a s
    have m1 := hwPre_le aPlain pre
    have m2 := hwPre_le bPlain (seqAssocHOL pre a)
    -- Case: the accumulator itself exits abnormally.
    rcases runPre : s.evaluateHOLFiniteState pre with ⟨rp,t⟩
    cases rp with
    | some x =>
      have hs : isSkip pre = false := by
        cases h : isSkip pre
        · rfl
        · have : pre = .skip := by cases pre <;> simp_all [isSkip]
          subst this; simp at runPre
      have ab := abnormal_visits (.seq aPlain bPlain) pre s hs (by rw [runPre]; simp)
      have e2 : s.evaluateHOLFiniteState (.seq pre (.seq a b)) = (some x, t) := by
        rw [evaluateHOLFiniteState_seq_line780, runPre]
      have aft : after pre (.seq a b) s = 0 := by simp [after, runPre]
      rw [e2, aft]
      simp only [prePart, hs, Bool.false_eq_true, if_false, exitOver]
      omega
    | none =>
    rw [split]
    have hb := ihb (seqAssocHOL pre a) s
    have ha := iha pre s
    have allEval : s.evaluateHOLFiniteState (.seq (seqAssocHOL pre a) b) =
        s.evaluateHOLFiniteState (.seq pre (.seq a b)) := by
      rw [← evaluateSeqAssocHOL, ← evaluateSeqAssocHOL, seqAssocHOL]
    rw [allEval] at hb
    cases hskip : isSkip (seqAssocHOL pre a) with
    | true =>
      have preSkip' : seqAssocHOL pre a = .skip := by cases h : seqAssocHOL pre a <;> simp_all [isSkip]
      have preSkip := seqAssoc_eq_skip aPlain pre preSkip'
      subst preSkip
      have aRun : s.evaluateHOLFiniteState a = (none, s) := by
        rw [← eval_seqAssoc_skip, preSkip', evaluateHOLFiniteState_skip]
      have dEq : delta .skip (.seq a b) = delta .skip b := by
        simp [delta, hwPre, isSkip, seqAssocHOL, preSkip']
      rw [dEq]
      rw [preSkip'] at hb ⊢
      simp only [prePart, isSkip, if_true, after, evaluateHOLFiniteState_skip, Nat.zero_add] at hb ⊢
      rw [controlSteps_seq, aRun]
      simp only
      omega
    | false =>
      have hb' : controlSteps (seqAssocHOL (seqAssocHOL pre a) b) s ≤
          1 + controlSteps (seqAssocHOL pre a) s + after (seqAssocHOL pre a) b s +
            exitOver (s.evaluateHOLFiniteState (.seq pre (.seq a b))).1 (delta (seqAssocHOL pre a) b) := by
        simpa [prePart, hskip] using hb
      have e1 : s.evaluateHOLFiniteState (.seq pre a) = t.evaluateHOLFiniteState a := by
        rw [evaluateHOLFiniteState_seq_line780, runPre]
      have e2 : s.evaluateHOLFiniteState (.seq pre (.seq a b)) = t.evaluateHOLFiniteState (.seq a b) := by
        rw [evaluateHOLFiniteState_seq_line780, runPre]
      have aft1 : after pre a s = controlSteps a t := by simp [after, runPre]
      have aft2 : after pre (.seq a b) s = controlSteps (.seq a b) t := by simp [after, runPre]
      have dsum : delta pre (.seq a b) = delta pre a + delta (seqAssocHOL pre a) b := by
        have hp' : hwPre (seqAssocHOL pre a) = hw (seqAssocHOL pre a) := by simp [hwPre, hskip]
        rw [hp'] at m2
        unfold delta; rw [split, hp']
        omega
      rw [e1, aft1] at ha
      rw [e2] at hb'
      rw [aft2, e2, controlSteps_seq, dsum]
      rcases runA : t.evaluateHOLFiniteState a with ⟨ra,u⟩
      rw [runA] at ha
      cases ra with
      | none =>
        have aftB : after (seqAssocHOL pre a) b s = controlSteps b u := by simp [after, preEval, e1, runA]
        have e3 : t.evaluateHOLFiniteState (.seq a b) = u.evaluateHOLFiniteState b := by
          rw [evaluateHOLFiniteState_seq_line780, runA]
        rw [aftB, e3] at hb'
        rw [e3]
        simp only [exitOver] at ha
        simp only
        have := exitOver_mono (u.evaluateHOLFiniteState b).1
          (show delta (seqAssocHOL pre a) b ≤ delta pre a + delta (seqAssocHOL pre a) b by omega)
        omega
      | some y =>
        have ab : (s.evaluateHOLFiniteState (seqAssocHOL pre a)).1 ≠ none := by
          rw [preEval, e1, runA]; simp
        have hA := abnormal_visits bPlain (seqAssocHOL pre a) s hskip ab
        have e3 : t.evaluateHOLFiniteState (.seq a b) = (some y, u) := by
          rw [evaluateHOLFiniteState_seq_line780, runA]
        rw [e3]
        simp only [exitOver] at ha ⊢
        omega

/-! Supported-level corollary with a compiled-code-only overhead. -/

private theorem supportedIn_plain {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : Plain (progToHOL program) := by
  induction supported <;> simp only [progToHOL] <;> constructor <;> assumption

private theorem frontend_hw {width : Nat} [NeZero width] {context : PanToCrepContextExact width} {p : ProgHOL width}
    (shape : FrontendProgram context p) : hw p ≤ CrepSteps.statementWeight (compileProgExactHOLW context p) := by
  induction shape with
  | skip | «break» | «continue» | tick | store | assign | ret =>
    simpa [hw] using CrepSteps.statementWeight_pos (compileProgExactHOLW _ _)
  | @decl ctxt name e body he hb ih =>
    obtain ⟨value,compiled⟩ := frontendDecl_compile ctxt name e body he
    rw [compiled]
    simp only [hw, CrepSteps.statementWeight]
    omega
  | @seq ctxt a b ha hb iha ihb =>
    simp only [hw,compileProgExactHOLW,CrepSteps.statementWeight]
    omega
  | @ite ctxt e a b he ha hb iha ihb =>
    obtain ⟨value,compiled⟩ := frontendScalar_compile he
    simp only [hw,compileProgExactHOLW,compileIfExactHOLW,compiled,CrepSteps.statementWeight]
    omega
  | @«while» ctxt e body he hb ih =>
    obtain ⟨value,compiled⟩ := frontendScalar_compile he
    simp only [hw,compileProgExactHOLW,compileWhileExactHOLW,compiled,CrepSteps.statementWeight]
    omega

/-- pan_simp's extra control visits are bounded by the weight of the simplified
body, charged only on an abnormal exit. -/
theorem supported_panSimp_controlSteps_simplified {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (s : PanSemStateFiniteExact 64 σ) :
    controlSteps (progToHOL (panSimpProg program)) s ≤
      controlSteps (progToHOL program) s +
        exitOver (s.evaluateHOLFiniteState (progToHOL program)).1 (hw (progToHOL (panSimpProg program))) := by
  rw [← supported_seqAssocHOL program supported]
  have h := seqAssoc_visits_delta (supportedIn_plain supported.1) .skip s
  simpa [prePart, isSkip, after, eval_seq_skip, delta, hwPre] using h

/-- Compiled-code-only form: the overhead is at most the statement weight of
the generated Crep body of the simplified program. -/
theorem supported_panSimp_controlSteps_compiled {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (context : PanToCrepContextExact 64) (s : PanSemStateFiniteExact 64 σ) :
    controlSteps (progToHOL (panSimpProg program)) s ≤
      controlSteps (progToHOL program) s +
        CrepSteps.statementWeight (compileProgExactHOLW context (progToHOL (panSimpProg program))) := by
  have h := supported_panSimp_controlSteps_simplified program supported s
  have w := frontend_hw (supported_frontend_shape (supported_panSimp program supported).1 context)
  exact h.trans (Nat.add_le_add_left ((over_le _ _).trans w) _)

end SteppedFlapjack.Concrete.SimpVisits
