import SteppedFlapjack.Concrete.SimpRun
import SteppedFlapjack.Concrete.ControlWeight

/-! pan_simp (seqAssoc) adds at most a static number of control
visits, charged only on an abnormal exit. -/
namespace SteppedFlapjack.Concrete.SimpVisits
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.Concrete

variable {width : Nat} [NeZero width] {σ : Type}

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

/-- Main accumulator bound for `seqAssocHOL`. -/
private theorem seqAssoc_visits {p : ProgHOL width} (plain : Plain p) :
    ∀ (pre : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      controlSteps (seqAssocHOL pre p) s ≤
        prePart pre s + after pre p s + exitOver (s.evaluateHOLFiniteState (.seq pre p)).1 (holWeight p) := by
  have skipForm : ∀ {q : ProgHOL width}, (∀ (pre : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      controlSteps (seqAssocHOL pre q) s ≤
        prePart pre s + after pre q s + exitOver (s.evaluateHOLFiniteState (.seq pre q)).1 (holWeight q)) →
      ∀ t : PanSemStateFiniteExact width σ, controlSteps (seqAssocHOL .skip q) t ≤
        controlSteps q t + exitOver (t.evaluateHOLFiniteState q).1 (holWeight q) := by
    intro q h t
    simpa [prePart, isSkip, after, eval_seq_skip] using h .skip t
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
    rw [show seqAssocHOL pre (.assign k n e : ProgHOL width) = smartSeqHOL pre (.assign k n e) by simp [seqAssocHOL]]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | ret e =>
    intro pre s
    rw [show seqAssocHOL pre (.return e : ProgHOL width) = smartSeqHOL pre (.return e) by simp [seqAssocHOL]]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | @dec n sh e body _ ih =>
    intro pre s
    rw [show seqAssocHOL pre (.dec n sh e body) = smartSeqHOL pre (.dec n sh e (seqAssocHOL .skip body)) by
      simp [seqAssocHOL]]
    apply smart_bound
    intro t
    apply dec_node
    intro u
    exact (skipForm ih u).trans (Nat.add_le_add_left (exitOver_mono _ (by simp [holWeight])) _)
  | @ite e a b _ _ iha ihb =>
    intro pre s
    rw [show seqAssocHOL pre (.ite e a b) =
      smartSeqHOL pre (.ite e (seqAssocHOL .skip a) (seqAssocHOL .skip b)) by simp [seqAssocHOL]]
    apply smart_bound
    intro t
    apply ite_node
    · intro u; exact (skipForm iha u).trans (Nat.add_le_add_left (exitOver_mono _ (by simp [holWeight]; omega)) _)
    · intro u; exact (skipForm ihb u).trans (Nat.add_le_add_left (exitOver_mono _ (by simp [holWeight])) _)
  | @«while» e body bodyPlain ih =>
    intro pre s
    rw [show seqAssocHOL pre (.while e body) = smartSeqHOL pre (.while e (seqAssocHOL .skip body)) by
      simp [seqAssocHOL]]
    apply smart_bound
    intro t
    apply while_node
    · intro u; exact (skipForm ih u).trans (Nat.add_le_add_left (exitOver_mono _ (by simp [holWeight])) _)
    · intro u; exact eval_seqAssoc_skip body u
    · exact plain_no_loop_exit bodyPlain
  | @seq a b aPlain bPlain iha ihb =>
    intro pre s
    rw [show seqAssocHOL pre (.seq a b) = seqAssocHOL (seqAssocHOL pre a) b by rw [seqAssocHOL]]
    have hb := ihb (seqAssocHOL pre a) s
    have ha := iha pre s
    have preEval : s.evaluateHOLFiniteState (seqAssocHOL pre a) = s.evaluateHOLFiniteState (.seq pre a) :=
      evaluateSeqAssocHOL pre a s
    have allEval : s.evaluateHOLFiniteState (.seq (seqAssocHOL pre a) b) =
        s.evaluateHOLFiniteState (.seq pre (.seq a b)) := by
      rw [← evaluateSeqAssocHOL, ← evaluateSeqAssocHOL, seqAssocHOL]
    rw [allEval] at hb
    have weight : holWeight (.seq a b) = 1 + holWeight a + holWeight b := by simp [holWeight]
    rw [weight]
    have boundA := over_le (s.evaluateHOLFiniteState (.seq pre a)).1 (holWeight a)
    have boundB := over_le (s.evaluateHOLFiniteState (.seq pre (.seq a b))).1 (holWeight b)
    cases hskip : isSkip (seqAssocHOL pre a) with
    | true =>
      have preSkip' : seqAssocHOL pre a = .skip := by cases h : seqAssocHOL pre a <;> simp_all [isSkip]
      have preSkip := seqAssoc_eq_skip aPlain pre preSkip'
      subst preSkip
      have aRun : s.evaluateHOLFiniteState a = (none, s) := by
        rw [← eval_seqAssoc_skip, preSkip', evaluateHOLFiniteState_skip]
      rw [preSkip'] at hb ⊢
      simp only [prePart, isSkip, if_true, after, evaluateHOLFiniteState_skip, Nat.zero_add] at hb ⊢
      rw [controlSteps_seq, aRun]
      simp only
      have := exitOver_mono (s.evaluateHOLFiniteState (.seq .skip (.seq a b))).1
        (show holWeight b ≤ 1 + holWeight a + holWeight b by omega)
      omega
    | false =>
      have hb' : controlSteps (seqAssocHOL (seqAssocHOL pre a) b) s ≤
          1 + controlSteps (seqAssocHOL pre a) s + after (seqAssocHOL pre a) b s +
            exitOver (s.evaluateHOLFiniteState (.seq pre (.seq a b))).1 (holWeight b) := by
        simpa [prePart, hskip] using hb
      have aft3 : after (seqAssocHOL pre a) b s = after (.seq pre a) b s := by simp [after, preEval]
      rw [aft3] at hb'
      rcases runPre : s.evaluateHOLFiniteState pre with ⟨rp,t⟩
      cases rp with
      | some x =>
        have e1 : s.evaluateHOLFiniteState (.seq pre a) = (some x, t) := by
          rw [evaluateHOLFiniteState_seq_line780, runPre]
        have e2 : s.evaluateHOLFiniteState (.seq pre (.seq a b)) = (some x, t) := by
          rw [evaluateHOLFiniteState_seq_line780, runPre]
        have aft1 : after pre a s = 0 := by simp [after, runPre]
        have aft2 : after pre (.seq a b) s = 0 := by simp [after, runPre]
        have aft4 : after (.seq pre a) b s = 0 := by simp [after, e1]
        rw [e1, aft1] at ha
        rw [e2, aft4] at hb'
        rw [aft2, e2]
        simp only [exitOver] at ha hb' ⊢
        omega
      | none =>
        have e1 : s.evaluateHOLFiniteState (.seq pre a) = t.evaluateHOLFiniteState a := by
          rw [evaluateHOLFiniteState_seq_line780, runPre]
        have e2 : s.evaluateHOLFiniteState (.seq pre (.seq a b)) = t.evaluateHOLFiniteState (.seq a b) := by
          rw [evaluateHOLFiniteState_seq_line780, runPre]
        have aft1 : after pre a s = controlSteps a t := by simp [after, runPre]
        have aft2 : after pre (.seq a b) s = controlSteps (.seq a b) t := by simp [after, runPre]
        rw [e1, aft1] at ha
        rw [e2] at hb'
        rw [aft2, e2, controlSteps_seq]
        simp only [after, e1] at hb'
        rcases runA : t.evaluateHOLFiniteState a with ⟨ra,u⟩
        rw [runA] at ha hb'
        cases ra with
        | none =>
          have e3 : t.evaluateHOLFiniteState (.seq a b) = u.evaluateHOLFiniteState b := by
            rw [evaluateHOLFiniteState_seq_line780, runA]
          rw [e3] at hb' ⊢
          simp only [exitOver] at ha
          simp only at hb' ⊢
          have := exitOver_mono (u.evaluateHOLFiniteState b).1
            (show holWeight b ≤ 1 + holWeight a + holWeight b by omega)
          omega
        | some y =>
          have e3 : t.evaluateHOLFiniteState (.seq a b) = (some y, u) := by
            rw [evaluateHOLFiniteState_seq_line780, runA]
          rw [e3] at hb' ⊢
          simp only [exitOver] at ha hb' ⊢
          omega

/-! Supported-level corollary. -/

private theorem supportedIn_plain {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : Plain (progToHOL program) := by
  induction supported <;> simp only [progToHOL] <;> constructor <;> assumption

private theorem supportedIn_weight {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : holWeight (progToHOL program) = programWeight program := by
  induction supported <;> simp_all [programWeight, holWeight, progToHOL, shapeToHOL]

/-- pan_simp adds no control visits to a supported run that ends normally,
and at most the static source weight to one that exits abnormally. -/
theorem supported_panSimp_controlSteps {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (s : PanSemStateFiniteExact 64 σ) :
    controlSteps (progToHOL (panSimpProg program)) s ≤
      controlSteps (progToHOL program) s +
        exitOver (s.evaluateHOLFiniteState (progToHOL program)).1 (programWeight program) := by
  rw [← supported_seqAssocHOL program supported, ← supportedIn_weight supported.1]
  have h := seqAssoc_visits (supportedIn_plain supported.1) .skip s
  simpa [prePart, isSkip, after, eval_seq_skip] using h

/-- Result-independent form. -/
theorem supported_panSimp_controlSteps_le {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (s : PanSemStateFiniteExact 64 σ) :
    controlSteps (progToHOL (panSimpProg program)) s ≤ controlSteps (progToHOL program) s + programWeight program :=
  (supported_panSimp_controlSteps program supported s).trans (Nat.add_le_add_left (over_le _ _) _)

end SteppedFlapjack.Concrete.SimpVisits
