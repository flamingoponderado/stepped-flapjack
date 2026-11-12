import SteppedFlapjack.Concrete.SimpRun
import SteppedFlapjack.CrepSteps.BranchStatic

/-! pan_simp (seqAssoc) overhead charged to the SIMPLIFIED body weight. -/
namespace SteppedFlapjack.Concrete.SimpVisits
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.Concrete

variable {width : Nat} [NeZero width] {σ : Type}

def hw : ProgHOL width → Nat
  | .dec _ _ _ body => 1 + hw body
  | .decCall _ _ _ _ body => 1 + hw body
  | .seq a b => 1 + hw a + hw b
  | .ite _ a b => 1 + hw a + hw b
  | .while _ body => 1 + hw body
  | _ => 1

/-- HOL images of supported, loop-exit-free bodies, including calls. -/
private inductive Plain : ProgHOL width → Prop
  | skip : Plain .skip
  | store (address value) : Plain (.store address value)
  | assign (k n e) : Plain (.assign k n e)
  | ret (e) : Plain (.return e)
  | tail (name args) : Plain (.call none name args)
  | decCall (name sh func args) {body} : Plain body → Plain (.decCall name sh func args body)
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
  | store address value =>
    intro s
    rw [evaluateHOLFiniteState_store]
    repeat' (first | split | simp)
  | assign k n e =>
    intro s
    rw [evaluateHOLFiniteState_assign]
    repeat' (first | split | simp)
  | ret e =>
    intro s
    rw [evaluateHOLFiniteState_return]
    repeat' (first | split | simp)
  | tail name args =>
    intro s
    rw [evaluateHOLFiniteState_call]
    repeat' (first | split | simp_all)
  | decCall name sh func args _ ih =>
    intro s
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    repeat' (first | split | simp_all)
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

private theorem decCall_node (n sh fn args body body' w)
    (hb : ∀ t : PanSemStateFiniteExact width σ,
      controlSteps body' t ≤ controlSteps body t + exitOver (t.evaluateHOLFiniteState body).1 w)
    (t : PanSemStateFiniteExact width σ) :
    controlSteps (.decCall n sh fn args body') t ≤ controlSteps (.decCall n sh fn args body) t +
      exitOver (t.evaluateHOLFiniteState (.decCall n sh fn args body)).1 w := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  cases argsEval : @evalListHOLFinite width σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) args with
  | none => rw [controlSteps.eq_def,controlSteps.eq_def (.decCall n sh fn args body)]; simp only [argsEval]; simp [exitOver]
  | some vs =>
    cases lookup : lookupCodeHOLFinite t.code.lookup fn vs with
    | none => rw [controlSteps.eq_def,controlSteps.eq_def (.decCall n sh fn args body)]; simp only [argsEval,lookup]; simp [exitOver]
    | some entry =>
      obtain ⟨callee,locals,rsh⟩ := entry
      by_cases clock : t.clock = 0
      · rw [controlSteps.eq_def,controlSteps.eq_def (.decCall n sh fn args body)]; simp only [argsEval,lookup,clock,if_true]; simp [exitOver]
      · rcases run : (callEntryStateHOLFinite t locals).evaluateHOLFiniteState callee with ⟨result,post⟩
        by_cases returned : ∃ value, result = some (.returned value)
        · obtain ⟨value,rfl⟩ := returned
          by_cases valid : shapeEqHOL (shapeOfHOLExact value) sh = true ∧ shapeEqHOL (shapeOfHOLExact value) rsh = true
          · rw [controlSteps_decCall_return n fn sh args body' t vs callee locals rsh value post argsEval lookup clock run valid.1 valid.2,
              controlSteps_decCall_return n fn sh args body t vs callee locals rsh value post argsEval lookup clock run valid.1 valid.2]
            have fixed : fixClockHOLFinite (callEntryStateHOLFinite t locals) (some (PanSemResultExact.returned value),post) = (some (PanSemResultExact.returned value),post) := by
              rw [← run,fixClockHOLFinite_evaluateState]
            simp only [lookup,if_neg clock,run,valid.1,valid.2,Bool.true_and,if_true,fixed]
            have bound := hb (setVarHOLFinite n value {post with locals := t.locals})
            omega
          · have bad : (shapeEqHOL (shapeOfHOLExact value) sh && shapeEqHOL (shapeOfHOLExact value) rsh) = false := by
              cases h₁ : shapeEqHOL (shapeOfHOLExact value) sh <;>
                cases h₂ : shapeEqHOL (shapeOfHOLExact value) rsh <;> simp_all
            have small (cont : ProgHOL width) : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
                ((callEntryStateHOLFinite t locals).clock,sizeOf callee)
                (t.clock,sizeOf (.decCall n sh fn args cont : ProgHOL width)) := by
              apply Prod.Lex.left
              simp only [callEntryStateHOLFinite]
              omega
            rw [controlSteps.eq_def,controlSteps.eq_def (.decCall n sh fn args body)]
            simp only [argsEval,lookup,clock,if_false,run,bad,Bool.false_eq_true,dif_pos (small body),dif_pos (small body'),exitOver]
            omega
        · have terminal : ∀ value, result ≠ some (.returned value) := by
            intro value h; exact returned ⟨value,h⟩
          rw [controlSteps_decCall_terminal n fn sh args body' t vs callee locals rsh result post argsEval lookup clock run terminal,
            controlSteps_decCall_terminal n fn sh args body t vs callee locals rsh result post argsEval lookup clock run terminal]
          exact Nat.le_add_right _ _

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
  | store address value =>
    intro pre h
    rw [show seqAssocHOL pre (.store address value : ProgHOL width) = smartSeqHOL pre (.store address value) by simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | assign k n e =>
    intro pre h
    rw [show seqAssocHOL pre (.assign k n e : ProgHOL width) = smartSeqHOL pre (.assign k n e) by simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | ret e =>
    intro pre h
    rw [show seqAssocHOL pre (.return e : ProgHOL width) = smartSeqHOL pre (.return e) by simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | tail name args =>
    intro pre h
    rw [show seqAssocHOL pre (.call none name args) = smartSeqHOL pre (.call none name args) by simp [seqAssocHOL]] at h
    cases smart_eq_skip h
  | @decCall n sh func args body _ _ =>
    intro pre h
    rw [show seqAssocHOL pre (.decCall n sh func args body) = smartSeqHOL pre (.decCall n sh func args (seqAssocHOL .skip body)) by simp [seqAssocHOL]] at h
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
  | store address value => intro pre; simp only [seqAssocHOL]; rw [smart_hw]; omega
  | assign k n e => intro pre; rw [seqAssoc_assign, smart_hw]; omega
  | ret e => intro pre; rw [seqAssoc_ret, smart_hw]; omega
  | tail name args => intro pre; simp only [seqAssocHOL]; rw [smart_hw]; omega
  | decCall n sh func args _ _ => intro pre; simp only [seqAssocHOL]; rw [smart_hw]; omega
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
  | store address value => intro pre s hs ab; unfold delta; simp only [seqAssocHOL]; exact leaf _ _ s hs ab
  | assign k n e => intro pre s hs ab; unfold delta; rw [seqAssoc_assign]; exact leaf _ _ s hs ab
  | ret e => intro pre s hs ab; unfold delta; rw [seqAssoc_ret]; exact leaf _ _ s hs ab
  | tail name args => intro pre s hs ab; unfold delta; simp only [seqAssocHOL]; exact leaf _ _ s hs ab
  | decCall n sh func args _ _ => intro pre s hs ab; unfold delta; simp only [seqAssocHOL]; exact leaf _ _ s hs ab
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
  | store address value =>
    intro pre s
    unfold delta; simp only [seqAssocHOL]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | assign k n e =>
    intro pre s
    unfold delta; rw [seqAssoc_assign]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | ret e =>
    intro pre s
    unfold delta; rw [seqAssoc_ret]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | tail name args =>
    intro pre s
    unfold delta; simp only [seqAssocHOL]
    exact smart_bound pre _ _ _ (fun t => Nat.le_add_right _ _) s
  | @decCall n sh func args body _ ih =>
    intro pre s
    unfold delta; simp only [seqAssocHOL]
    apply smart_bound
    intro t
    apply decCall_node
    intro u
    refine (skipForm ih u).trans (Nat.add_le_add_left (exitOver_mono _ ?_) _)
    have := smartDelta pre (.decCall n sh func args (seqAssocHOL .skip body))
    simp only [hw] at this; omega
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

private theorem callSupportedIn_plain {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : Plain (progToHOL program) := by
  induction supported with
  | base h => exact supportedIn_plain h
  | tail name args scalar => simp only [progToHOL]; exact .tail _ _
  | call dest name args scalar cont ih => simp only [progToHOL,shapeToHOL]; exact .decCall _ _ _ _ ih
  | decl name scalar body ih => simp only [progToHOL,shapeToHOL]; exact .dec _ _ _ ih
  | seq a b iha ihb => simp only [progToHOL]; exact .seq iha ihb
  | ite scalar a b iha ihb => simp only [progToHOL]; exact .ite _ iha ihb
  | «while» scalar body ih => simp only [progToHOL]; exact .while _ ih

/-- Reassociation on a fixed function table has an explicit overhead, including
ordinary calls and their continuations. -/
theorem callSupported_panSimp_controlSteps {scope : List VarName} {σ : Type}
    {program : Prog (RiscV.Word 64)} (supported : CallSupportedIn scope program)
    (s : PanSemStateFiniteExact 64 σ) :
    controlSteps (progToHOL (panSimpProg program)) s ≤
      controlSteps (progToHOL program) s +
        exitOver (s.evaluateHOLFiniteState (progToHOL program)).1 (hw (progToHOL (panSimpProg program))) := by
  rw [← callSupported_seqAssocHOL supported]
  have h := seqAssoc_visits_delta (callSupportedIn_plain supported) .skip s
  simpa [prePart,isSkip,after,eval_seq_skip,delta,hwPre] using h

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

private theorem callFrontend_hw {width : Nat} [NeZero width] {context : PanToCrepContextExact width} {p : ProgHOL width}
    (shape : CallFrontend context p) : hw p ≤ CrepSteps.statementWeight (compileProgExactHOLW context p) := by
  induction shape with
  | base h => exact frontend_hw h
  | tail => simpa [hw] using CrepSteps.statementWeight_pos (compileProgExactHOLW _ _)
  | @decCall ctxt name sh fn args cont ha hb ih =>
    rw [decCall_statementWeight]
    simp only [hw]
    omega
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

/-- Reassociation overhead is bounded by the actual generated Crep weight for
call-aware frontend programs. -/
theorem callSupported_panSimp_controlSteps_compiled {scope : List VarName} {σ : Type}
    {program : Prog (RiscV.Word 64)} (supported : CallSupportedIn scope program)
    (context : PanToCrepContextExact 64)
    (shape : CallFrontend context (progToHOL (panSimpProg program))) (s : PanSemStateFiniteExact 64 σ) :
    controlSteps (progToHOL (panSimpProg program)) s ≤
      controlSteps (progToHOL program) s +
        CrepSteps.statementWeight (compileProgExactHOLW context (progToHOL (panSimpProg program))) := by
  have h := callSupported_panSimp_controlSteps supported s
  have w := callFrontend_hw shape
  exact h.trans (Nat.add_le_add_left ((over_le _ _).trans w) _)

private theorem tailTableStep {scope : List VarName} {σ : Type} {p : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope p) (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel s.code code) (function : MlS) (args : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (argsEval : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (progToHOL p,locals,shape))
    (clock : s.clock ≠ 0) (factor : Nat)
    (weight : hw (progToHOL (panSimpProg p)) + 1 ≤ factor)
    (calleeBound : controlSteps (progToHOL p) (callEntryStateHOLFinite {s with code := code} locals) ≤
      factor * controlSteps (progToHOL p) (callEntryStateHOLFinite s locals)) :
    controlSteps (.call none function args) {s with code := code} ≤
      factor * controlSteps (.call none function args) s := by
  have targetArgs : @evalListHOLFinite 64 σ _ {s with code := code}
      (fun a => Classical.propDecidable (s.memaddrs a)) args = some values := by
    rw [PanSimp.evalListCodeUpd, argsEval]
  have targetFound : lookupCodeHOLFinite code.lookup function values =
      some (progToHOL (panSimpProg p),locals,shape) := by
    rw [PanSimp.lookupCodeRel s.code code rel,found]
    simp [callSupported_panSimp_hol supported]
  rw [controlSteps_tailCall function args s values (progToHOL p) locals shape argsEval found clock]
  rw [controlSteps_tailCall function args {s with code := code} values (progToHOL (panSimpProg p)) locals shape
    targetArgs targetFound clock]
  have reassoc := callSupported_panSimp_controlSteps supported (callEntryStateHOLFinite {s with code := code} locals)
  have extra : exitOver ((callEntryStateHOLFinite {s with code := code} locals).evaluateHOLFiniteState (progToHOL p)).1
      (hw (progToHOL (panSimpProg p))) ≤ hw (progToHOL (panSimpProg p)) := by
    cases ((callEntryStateHOLFinite {s with code := code} locals).evaluateHOLFiniteState (progToHOL p)).1 <;> simp [exitOver]
  simp only [Nat.mul_add,Nat.mul_one]
  omega

private theorem decCallTableReturnStep {scope : List VarName} {σ : Type} {p : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope p) (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel s.code code) (dest function : MlS) (destShape : ShapeHOL)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL) (value : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 σ)
    (argsEval : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (progToHOL p,locals,returnShape))
    (clock : s.clock ≠ 0)
    (run : (callEntryStateHOLFinite s locals).evaluateHOLFiniteState (progToHOL p) = (some (.returned value),post))
    (valid : shapeEqHOL (shapeOfHOLExact value) destShape = true)
    (returnValid : shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (factor : Nat) (weight : hw (progToHOL (panSimpProg p)) + 1 ≤ factor)
    (calleeBound : controlSteps (progToHOL p) (callEntryStateHOLFinite {s with code := code} locals) ≤
      factor * controlSteps (progToHOL p) (callEntryStateHOLFinite s locals))
    (contBound : controlSteps cont {setVarHOLFinite dest value {post with locals := s.locals} with code := code} ≤
      factor * controlSteps cont (setVarHOLFinite dest value {post with locals := s.locals})) :
    controlSteps (.decCall dest destShape function args cont) {s with code := code} ≤
      factor * controlSteps (.decCall dest destShape function args cont) s := by
  have targetArgs : @evalListHOLFinite 64 σ _ {s with code := code}
      (fun a => Classical.propDecidable (s.memaddrs a)) args = some values := by
    rw [PanSimp.evalListCodeUpd, argsEval]
  have targetFound : lookupCodeHOLFinite code.lookup function values =
      some (progToHOL (panSimpProg p),locals,returnShape) := by
    rw [PanSimp.lookupCodeRel s.code code rel,found]
    simp [callSupported_panSimp_hol supported]
  obtain ⟨targetRun,_⟩ := PanSimp.codeSim_body s locals (progToHOL p) code rel
    (PanSimp.codeSimAll (progToHOL p) {s.decClockHOLFinite with locals := locals})
    (some (.returned value)) post run (by simp)
  rw [callSupported_panSimp_hol supported] at targetRun
  rw [controlSteps_decCall_return dest function destShape args cont s values (progToHOL p) locals returnShape
    value post argsEval found clock run valid returnValid]
  rw [controlSteps_decCall_return dest function destShape args cont {s with code := code} values
    (progToHOL (panSimpProg p)) locals returnShape value {post with code := code} targetArgs targetFound clock
    targetRun valid returnValid]
  have fixed : fixClockHOLFinite (callEntryStateHOLFinite s locals) (some (PanSemResultExact.returned value),post) =
      (some (PanSemResultExact.returned value),post) := by rw [← run,fixClockHOLFinite_evaluateState]
  have fixedTarget : fixClockHOLFinite (callEntryStateHOLFinite {s with code := code} locals)
      (some (PanSemResultExact.returned value),{post with code := code}) = (some (PanSemResultExact.returned value),{post with code := code}) := by
    rw [← targetRun,fixClockHOLFinite_evaluateState]
  simp only [fixed,fixedTarget]
  have reassoc := callSupported_panSimp_controlSteps supported (callEntryStateHOLFinite {s with code := code} locals)
  have extra : exitOver ((callEntryStateHOLFinite {s with code := code} locals).evaluateHOLFiniteState (progToHOL p)).1
      (hw (progToHOL (panSimpProg p))) ≤ hw (progToHOL (panSimpProg p)) := by
    cases ((callEntryStateHOLFinite {s with code := code} locals).evaluateHOLFiniteState (progToHOL p)).1 <;> simp [exitOver]
  simp only [Nat.mul_add,Nat.mul_one]
  have contBound' : controlSteps cont (setVarHOLFinite dest value {post with locals := s.locals, code := code}) ≤
      factor * controlSteps cont (setVarHOLFinite dest value {post with locals := s.locals}) := by
    simpa [setVarHOLFinite] using contBound
  omega

private theorem decCallTableTerminalStep {scope : List VarName} {σ : Type} {p : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope p) (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel s.code code) (dest function : MlS) (destShape : ShapeHOL)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 σ)
    (argsEval : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (progToHOL p,locals,returnShape))
    (clock : s.clock ≠ 0)
    (run : (callEntryStateHOLFinite s locals).evaluateHOLFiniteState (progToHOL p) = (result,post))
    (nonerror : result ≠ some .error) (terminal : ∀ value, result ≠ some (.returned value))
    (factor : Nat) (weight : hw (progToHOL (panSimpProg p)) + 1 ≤ factor)
    (calleeBound : controlSteps (progToHOL p) (callEntryStateHOLFinite {s with code := code} locals) ≤
      factor * controlSteps (progToHOL p) (callEntryStateHOLFinite s locals)) :
    controlSteps (.decCall dest destShape function args cont) {s with code := code} ≤
      factor * controlSteps (.decCall dest destShape function args cont) s := by
  have targetArgs : @evalListHOLFinite 64 σ _ {s with code := code}
      (fun a => Classical.propDecidable (s.memaddrs a)) args = some values := by
    rw [PanSimp.evalListCodeUpd, argsEval]
  have targetFound : lookupCodeHOLFinite code.lookup function values =
      some (progToHOL (panSimpProg p),locals,returnShape) := by
    rw [PanSimp.lookupCodeRel s.code code rel,found]
    simp [callSupported_panSimp_hol supported]
  obtain ⟨targetRun,_⟩ := PanSimp.codeSim_body s locals (progToHOL p) code rel
    (PanSimp.codeSimAll (progToHOL p) {s.decClockHOLFinite with locals := locals}) result post run nonerror
  rw [callSupported_panSimp_hol supported] at targetRun
  rw [controlSteps_decCall_terminal dest function destShape args cont s values (progToHOL p) locals returnShape
    result post argsEval found clock run terminal]
  rw [controlSteps_decCall_terminal dest function destShape args cont {s with code := code} values
    (progToHOL (panSimpProg p)) locals returnShape result {post with code := code} targetArgs targetFound clock
    targetRun terminal]
  have reassoc := callSupported_panSimp_controlSteps supported (callEntryStateHOLFinite {s with code := code} locals)
  have extra : exitOver ((callEntryStateHOLFinite {s with code := code} locals).evaluateHOLFiniteState (progToHOL p)).1
      (hw (progToHOL (panSimpProg p))) ≤ hw (progToHOL (panSimpProg p)) := by
    cases ((callEntryStateHOLFinite {s with code := code} locals).evaluateHOLFiniteState (progToHOL p)).1 <;> simp [exitOver]
  simp only [Nat.mul_add,Nat.mul_one]
  omega

private theorem tableSeqStep {σ : Type} (a b : ProgHOL 64) (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel s.code code) (result : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 σ) (run : s.evaluateHOLFiniteState a = (result,post))
    (nonerror : result ≠ some .error) (factor : Nat) (factorPositive : 1 ≤ factor)
    (firstBound : controlSteps a {s with code := code} ≤ factor * controlSteps a s)
    (secondBound : result = none → controlSteps b {post with code := code} ≤ factor * controlSteps b post) :
    controlSteps (.seq a b) {s with code := code} ≤ factor * controlSteps (.seq a b) s := by
  obtain ⟨targetRun,_⟩ := PanSimp.codeSimAll a s result post code run nonerror rel
  rw [controlSteps_seq,controlSteps_seq,run,targetRun]
  cases result with
  | none =>
    have hb := secondBound rfl
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  | some r =>
    simp only [Nat.mul_add,Nat.mul_one]
    omega

private theorem tableIteStep {σ : Type} (condition : ExpHOL 64) (a b : ProgHOL 64) (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (factor : Nat) (factorPositive : 1 ≤ factor)
    (reachedBound : ∀ w, @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) condition =
      some (.val (.word w)) →
      if w ≠ 0 then controlSteps a {s with code := code} ≤ factor * controlSteps a s
      else controlSteps b {s with code := code} ≤ factor * controlSteps b s) :
    controlSteps (.ite condition a b) {s with code := code} ≤ factor * controlSteps (.ite condition a b) s := by
  have evaluated := @evalHOLFinite_upd_code_eq 64 σ _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) code condition
  change @evalHOLExact 64 σ _ ({s with code := code} : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) condition =
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) condition at evaluated
  rw [controlSteps_ite,controlSteps_ite,evaluated]
  split
  next w h =>
    have reached := reachedBound w h
    split_ifs at * <;> simp_all only [Nat.mul_add,Nat.mul_one] <;> omega
  next => simp; omega

private theorem tableDeclStep {σ : Type} (name : MlS) (shape : ShapeHOL) (e : ExpHOL 64) (body : ProgHOL 64)
    (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (factor : Nat) (factorPositive : 1 ≤ factor)
    (bodyBound : ∀ v, @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      shapeEqHOL shape (shapeOfHOLExact v) = true →
      controlSteps body (setVarHOLFinite name v {s with code := code}) ≤
        factor * controlSteps body (setVarHOLFinite name v s)) :
    controlSteps (.dec name shape e body) {s with code := code} ≤ factor * controlSteps (.dec name shape e body) s := by
  have evaluated := @evalHOLFinite_upd_code_eq 64 σ _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) code e
  change @evalHOLExact 64 σ _ ({s with code := code} : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e =
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e at evaluated
  cases h : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
  | none =>
    rw [controlSteps.eq_def,controlSteps.eq_def (.dec name shape e body)]
    simp only [evaluated,h]
    omega
  | some value =>
    by_cases valid : shapeEqHOL shape (shapeOfHOLExact value) = true
    · have targetEval : @evalHOLExact 64 σ _ ({s with code := code} : PanSemStateFiniteExact 64 σ).toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) e = some value := evaluated.trans h
      rw [controlSteps_dec name shape e body _ value targetEval valid,controlSteps_dec name shape e body s value h valid]
      have bound := bodyBound value h valid
      simp only [Nat.mul_add,Nat.mul_one]
      omega
    · rw [controlSteps.eq_def,controlSteps.eq_def (.dec name shape e body)]
      simp only [evaluated,h,valid,Bool.false_eq_true,if_false]
      omega

private theorem tableWhileStep {σ : Type} (condition : ExpHOL 64) (body : ProgHOL 64) (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel s.code code) (word : BitVec 64)
    (test : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word word)))
    (nonzero : word ≠ 0) (clock : s.clock ≠ 0)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 σ)
    (run : s.decClockHOLFinite.evaluateHOLFiniteState body = (result,post)) (nonerror : result ≠ some .error)
    (factor : Nat) (factorPositive : 1 ≤ factor)
    (bodyBound : controlSteps body {s.decClockHOLFinite with code := code} ≤ factor * controlSteps body s.decClockHOLFinite)
    (loopBound : result = none ∨ result = some .continue →
      controlSteps (.while condition body) {post with code := code} ≤ factor * controlSteps (.while condition body) post) :
    controlSteps (.while condition body) {s with code := code} ≤ factor * controlSteps (.while condition body) s := by
  have evaluated := @evalHOLFinite_upd_code_eq 64 σ _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) code condition
  change @evalHOLExact 64 σ _ ({s with code := code} : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) condition =
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) condition at evaluated
  have entryRel : PanSimp.CodeRel s.decClockHOLFinite.code code := rel
  obtain ⟨targetRun,_⟩ := PanSimp.codeSimAll body s.decClockHOLFinite result post code run nonerror entryRel
  have targetRun' : ({s with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite.evaluateHOLFiniteState body =
      (result,{post with code := code}) := by simpa [decClockHOLFinite] using targetRun
  have bodyBound' : controlSteps body ({s with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite ≤
      factor * controlSteps body s.decClockHOLFinite := by simpa [decClockHOLFinite] using bodyBound
  rw [controlSteps_while,controlSteps_while,evaluated,test]
  simp only [if_pos (And.intro nonzero clock),targetRun',run,Nat.mul_add,Nat.mul_one]
  cases result with
  | none => have bound := loopBound (Or.inl rfl); simp only; omega
  | some r =>
    cases r with
    | «continue» => have bound := loopBound (Or.inr rfl); simp only; omega
    | «break» | error | timeOut | returned _ | finalFfi _ | exception _ _ => simp only; omega

/-- Compiled-code-only form: the overhead is at most the statement weight of
the generated Crep body of the simplified program. -/
theorem supported_panSimp_controlSteps_compiled {σ : Type} (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
    (context : PanToCrepContextExact 64) (s : PanSemStateFiniteExact 64 σ) :
    controlSteps (progToHOL (panSimpProg program)) s ≤
      controlSteps (progToHOL program) s +
        CrepSteps.statementWeight (compileProgExactHOLW context (progToHOL (panSimpProg program))) := by
  exact callSupported_panSimp_controlSteps_compiled (.base supported.1) context
    (.base (supported_frontend_shape (supported_panSimp program supported).1 context)) s


private theorem tailBodyNonerror {σ : Type} (s : PanSemStateFiniteExact 64 σ)
    (function : MlS) (args : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (argsEval : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (body,locals,shape)) (clock : s.clock ≠ 0)
    (nonerror : (s.evaluateHOLFiniteState (.call none function args)).1 ≠ some .error) :
    ((callEntryStateHOLFinite s locals).evaluateHOLFiniteState body).1 ≠ some .error := by
  intro bad
  rw [evaluateHOLFiniteState_call] at nonerror
  simp only [argsEval,found,if_neg clock] at nonerror
  rcases run : (callEntryStateHOLFinite s locals).evaluateHOLFiniteState body with ⟨result,post⟩
  rw [run] at bad
  simp only at bad
  subst result
  simp [run] at nonerror

private theorem decCallBodyNonerror {σ : Type} (s : PanSemStateFiniteExact 64 σ)
    (dest function : MlS) (destShape : ShapeHOL) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (values : List (ValueHOL 64)) (body : ProgHOL 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (argsEval : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (body,locals,shape)) (clock : s.clock ≠ 0)
    (nonerror : (s.evaluateHOLFiniteState (.decCall dest destShape function args cont)).1 ≠ some .error) :
    ((callEntryStateHOLFinite s locals).evaluateHOLFiniteState body).1 ≠ some .error := by
  intro bad
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at nonerror
  simp only [argsEval,found,if_neg clock] at nonerror
  rcases run : (callEntryStateHOLFinite s locals).evaluateHOLFiniteState body with ⟨result,post⟩
  rw [run] at bad
  simp only at bad
  subst result
  simp [run] at nonerror

def SimpTableSupported (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (factor : Nat) : Prop :=
  ∀ name values body locals rsh, lookupCodeHOLFinite code.lookup name values = some (body,locals,rsh) →
    ∃ scope, ∃ program : Prog (RiscV.Word 64), body = progToHOL program ∧ CallSupportedIn scope program ∧
      hw (progToHOL (panSimpProg program)) + 1 ≤ factor

private theorem plainTableBound {σ : Type} (factor : Nat) (positive : 1 ≤ factor) :
    ∀ p : ProgHOL 64, Plain p → ∀ (s : PanSemStateFiniteExact 64 σ)
      (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)),
      PanSimp.CodeRel s.code code → SimpTableSupported s.code factor →
      (s.evaluateHOLFiniteState p).1 ≠ some .error →
      controlSteps p {s with code := code} ≤ factor * controlSteps p s := by
  intro p shape s code rel table nonerror
  induction clockEq : s.clock using Nat.strongRecOn generalizing p s with
  | _ clock clockIH =>
    induction shape generalizing s with
    | skip =>
      rw [controlSteps_skip,controlSteps_skip]
      simpa using positive
    | store address value =>
      simpa only [controlSteps.eq_def,Nat.add_zero,Nat.mul_one] using positive
    | assign k name e =>
      simpa only [controlSteps.eq_def,Nat.add_zero,Nat.mul_one] using positive
    | ret e =>
      simpa only [controlSteps.eq_def,Nat.add_zero,Nat.mul_one] using positive
    | tail name args =>
      rw [← clockEq]
      have targetArgs := PanSimp.evalListCodeUpd code s args
      cases argsEval : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
      | none =>
        rw [controlSteps.eq_def,controlSteps.eq_def (.call none name args)]
        simp only [targetArgs,argsEval,Nat.add_zero,Nat.mul_one]
        exact positive
      | some values =>
        cases found : lookupCodeHOLFinite s.code.lookup name values with
        | none =>
          have targetFound := PanSimp.lookupCodeRel s.code code rel name values
          rw [found] at targetFound
          simp only [Option.map_none] at targetFound
          rw [controlSteps.eq_def,controlSteps.eq_def (.call none name args)]
          simp only [targetArgs,argsEval,targetFound,found,Nat.add_zero,Nat.mul_one]
          exact positive
        | some entry =>
          obtain ⟨body,locals,rsh⟩ := entry
          by_cases noClock : s.clock = 0
          · have targetFound := PanSimp.lookupCodeRel s.code code rel name values
            rw [found] at targetFound
            simp only [Option.map_some] at targetFound
            rw [controlSteps.eq_def,controlSteps.eq_def (.call none name args)]
            simp only [targetArgs,argsEval,targetFound,found,if_pos noClock,Nat.add_zero,Nat.mul_one]
            exact positive
          · obtain ⟨scope,program,bodyEq,supported,weight⟩ := table name values body locals rsh found
            subst body
            have bodyNonerror := tailBodyNonerror s name args values (progToHOL program) locals rsh
              argsEval found noClock nonerror
            have entryRel : PanSimp.CodeRel (callEntryStateHOLFinite s locals).code code := rel
            have entryTable : SimpTableSupported (callEntryStateHOLFinite s locals).code factor := table
            have entrySmall : (callEntryStateHOLFinite s locals).clock < clock := by
              simp only [callEntryStateHOLFinite]
              omega
            have bound := clockIH (callEntryStateHOLFinite s locals).clock entrySmall
              (progToHOL program) (callSupportedIn_plain supported) (callEntryStateHOLFinite s locals)
              entryRel entryTable bodyNonerror rfl
            apply tailTableStep supported s code rel name args values locals rsh argsEval found noClock factor weight
            simpa [callEntryStateHOLFinite] using bound
    | @decCall name sh fn args cont bodyShape bodyIH =>
      rw [← clockEq]
      have targetArgs := PanSimp.evalListCodeUpd code s args
      cases argsEval : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
      | none =>
        rw [controlSteps.eq_def,controlSteps.eq_def (.decCall name sh fn args cont)]
        simp only [targetArgs,argsEval,Nat.add_zero,Nat.mul_one]
        exact positive
      | some values =>
        cases found : lookupCodeHOLFinite s.code.lookup fn values with
        | none =>
          have targetFound := PanSimp.lookupCodeRel s.code code rel fn values
          rw [found] at targetFound
          simp only [Option.map_none] at targetFound
          rw [controlSteps.eq_def,controlSteps.eq_def (.decCall name sh fn args cont)]
          simp only [targetArgs,argsEval,targetFound,found,Nat.add_zero,Nat.mul_one]
          exact positive
        | some entry =>
          obtain ⟨body,locals,rsh⟩ := entry
          by_cases noClock : s.clock = 0
          · have targetFound := PanSimp.lookupCodeRel s.code code rel fn values
            rw [found] at targetFound
            simp only [Option.map_some] at targetFound
            rw [controlSteps.eq_def,controlSteps.eq_def (.decCall name sh fn args cont)]
            simp only [targetArgs,argsEval,targetFound,found,if_pos noClock,Nat.add_zero,Nat.mul_one]
            exact positive
          · obtain ⟨scope,program,bodyEq,supported,weight⟩ := table fn values body locals rsh found
            subst body
            have bodyNonerror := decCallBodyNonerror s name fn sh args cont values (progToHOL program) locals rsh
              argsEval found noClock nonerror
            have entryRel : PanSimp.CodeRel (callEntryStateHOLFinite s locals).code code := rel
            have entryTable : SimpTableSupported (callEntryStateHOLFinite s locals).code factor := table
            have entrySmall : (callEntryStateHOLFinite s locals).clock < clock := by
              simp only [callEntryStateHOLFinite]
              omega
            have bodyBound := clockIH (callEntryStateHOLFinite s locals).clock entrySmall
              (progToHOL program) (callSupportedIn_plain supported) (callEntryStateHOLFinite s locals)
              entryRel entryTable bodyNonerror rfl
            have bodyBound' : controlSteps (progToHOL program) (callEntryStateHOLFinite {s with code := code} locals) ≤
                factor * controlSteps (progToHOL program) (callEntryStateHOLFinite s locals) := by
              simpa [callEntryStateHOLFinite] using bodyBound
            rcases run : (callEntryStateHOLFinite s locals).evaluateHOLFiniteState (progToHOL program) with ⟨result,post⟩
            have bodyResultNonerror : result ≠ some .error := by simpa [run] using bodyNonerror
            by_cases returned : ∃ value, result = some (.returned value)
            · obtain ⟨value,rfl⟩ := returned
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at nonerror
              simp only [argsEval,found,if_neg noClock,run] at nonerror
              by_cases valid : shapeEqHOL (shapeOfHOLExact value) sh = true ∧ shapeEqHOL (shapeOfHOLExact value) rsh = true
              · simp only [valid.1,valid.2,Bool.true_and,if_true] at nonerror
                let next := setVarHOLFinite name value {post with locals := s.locals}
                have nextNonerror : (next.evaluateHOLFiniteState cont).1 ≠ some .error := nonerror
                have postCode := (PanSimp.codeSimAll (progToHOL program) (callEntryStateHOLFinite s locals)
                  (some (.returned value)) post code run (by simp) entryRel).2
                have nextRel : PanSimp.CodeRel next.code code := by simpa [next,setVarHOLFinite,postCode,callEntryStateHOLFinite] using rel
                have nextTable : SimpTableSupported next.code factor := by simpa [next,setVarHOLFinite,postCode,callEntryStateHOLFinite] using table
                have nextSmall : next.clock < clock := by
                  have h := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s locals) (progToHOL program)
                  rw [run] at h
                  simp only [next,setVarHOLFinite,callEntryStateHOLFinite] at h ⊢
                  omega
                have nextBound := clockIH next.clock nextSmall cont bodyShape next nextRel nextTable nextNonerror rfl
                apply decCallTableReturnStep supported s code rel name fn sh args cont values locals rsh value post
                  argsEval found noClock run valid.1 valid.2 factor weight bodyBound'
                simpa [next] using nextBound
              · have bad : (shapeEqHOL (shapeOfHOLExact value) sh && shapeEqHOL (shapeOfHOLExact value) rsh) = false := by
                  cases h₁ : shapeEqHOL (shapeOfHOLExact value) sh <;>
                    cases h₂ : shapeEqHOL (shapeOfHOLExact value) rsh <;> simp_all
                simp only [bad,Bool.false_eq_true,if_false] at nonerror
                exact absurd rfl nonerror
            · have terminal : ∀ value, result ≠ some (.returned value) := by
                intro value h; exact returned ⟨value,h⟩
              exact decCallTableTerminalStep supported s code rel name fn sh args cont values locals rsh result post
                argsEval found noClock run bodyResultNonerror terminal factor weight bodyBound'
    | @dec name sh e body bodyShape bodyIH =>
      rw [← clockEq]
      apply tableDeclStep name sh e body s code factor positive
      intro value evaluated valid
      have bodyNonerror : ((setVarHOLFinite name value s).evaluateHOLFiniteState body).1 ≠ some .error := by
        rw [evaluateHOLFiniteState_dec_total] at nonerror
        simp only [evaluated,valid,if_true] at nonerror
        exact nonerror
      have bodyRel : PanSimp.CodeRel (setVarHOLFinite name value s).code code := by simpa [setVarHOLFinite] using rel
      have bodyTable : SimpTableSupported (setVarHOLFinite name value s).code factor := by simpa [setVarHOLFinite] using table
      have bodyClock : (setVarHOLFinite name value s).clock = clock := by simpa [setVarHOLFinite] using clockEq
      have bound := bodyIH (setVarHOLFinite name value s) bodyRel bodyTable bodyNonerror bodyClock
      simpa [setVarHOLFinite,clockEq] using bound
    | @seq a b ashape bshape aIH bIH =>
      rw [← clockEq]
      rcases run : s.evaluateHOLFiniteState a with ⟨result,post⟩
      have firstNonerror : result ≠ some .error := by
        intro bad
        rw [evaluateHOLFiniteState_seq_line780,run,bad] at nonerror
        exact nonerror rfl
      have first := aIH s rel table (by simpa [run] using firstNonerror) clockEq
      have first' : controlSteps a {s with code := code} ≤ factor * controlSteps a s := by
        simpa [clockEq] using first
      apply tableSeqStep a b s code rel result post run firstNonerror factor positive first'
      intro done
      subst result
      have nextNonerror : (post.evaluateHOLFiniteState b).1 ≠ some .error := by
        rw [evaluateHOLFiniteState_seq_line780,run] at nonerror
        exact nonerror
      have postCode := (PanSimp.codeSimAll a s none post code run (by simp) rel).2
      have postRel : PanSimp.CodeRel post.code code := by rw [postCode]; exact rel
      have postTable : SimpTableSupported post.code factor := by rw [postCode]; exact table
      have postClock : post.clock ≤ clock := by
        have h := evaluateHOLFiniteState_clock_le s a
        rw [run] at h
        simpa [clockEq] using h
      by_cases same : post.clock = clock
      · have bound := bIH post postRel postTable nextNonerror same
        simpa [same] using bound
      · have bound := clockIH post.clock (by omega) b bshape post postRel postTable nextNonerror rfl
        simpa using bound
    | @ite e a b ashape bshape aIH bIH =>
      rw [← clockEq]
      apply tableIteStep e a b s code factor positive
      intro word evaluated
      rw [evaluateHOLFiniteState_ite] at nonerror
      simp only [evaluated] at nonerror
      by_cases nonzero : word ≠ 0
      · simp only [if_neg nonzero] at nonerror
        simp only [if_pos nonzero]
        have bound := aIH s rel table nonerror clockEq
        simpa [clockEq] using bound
      · have zero : word = 0 := Classical.not_not.mp nonzero
        simp only [if_pos zero] at nonerror
        simp only [if_neg nonzero]
        have bound := bIH s rel table nonerror clockEq
        simpa [clockEq] using bound
    | @«while» e body bodyShape bodyIH =>
      rw [← clockEq]
      have evalSame := @evalHOLFinite_upd_code_eq 64 σ _ s
        (fun address => Classical.propDecidable (s.memaddrs address)) code e
      change @evalHOLExact 64 σ _ ({s with code := code} : PanSemStateFiniteExact 64 σ).toExact
          (fun a => Classical.propDecidable (s.memaddrs a)) e =
        @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e at evalSame
      cases tested : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
      | none =>
        rw [controlSteps_while,controlSteps_while,evalSame,tested]
        simpa using positive
      | some v =>
        rcases v with ⟨⟨word⟩⟩ | _ | _
        · by_cases guard : word ≠ 0 ∧ s.clock ≠ 0
          · have bodyRun := s.decClockHOLFinite.evaluateHOLFiniteState body
            rcases run : s.decClockHOLFinite.evaluateHOLFiniteState body with ⟨result,post⟩
            have bodyNonerror : result ≠ some .error := by
              intro bad
              rw [evaluateHOLFiniteState_while_fixClockRewrite] at nonerror
              change @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word word)) at tested
              simp only [tested,if_pos guard.1,if_neg guard.2,run,bad] at nonerror
              exact nonerror rfl
            have entryRel : PanSimp.CodeRel s.decClockHOLFinite.code code := rel
            have entryTable : SimpTableSupported s.decClockHOLFinite.code factor := table
            have entrySmall : s.decClockHOLFinite.clock < clock := by simp only [decClockHOLFinite]; omega
            have bodyBound := clockIH s.decClockHOLFinite.clock entrySmall body bodyShape s.decClockHOLFinite
              entryRel entryTable (by simpa [run] using bodyNonerror) rfl
            apply tableWhileStep e body s code rel word tested guard.1 guard.2 result post run bodyNonerror
              factor positive (by simpa using bodyBound)
            intro continues
            have loopNonerror : (post.evaluateHOLFiniteState (.while e body)).1 ≠ some .error := by
              rw [evaluateHOLFiniteState_while_fixClockRewrite] at nonerror
              change @evalHOLFinite 64 σ _ s (fun address => Classical.propDecidable (s.memaddrs address)) e = some (.val (.word word)) at tested
              rcases continues with h | h
              · simp only [tested,if_pos guard.1,if_neg guard.2,run,h] at nonerror
                exact nonerror
              · simp only [tested,if_pos guard.1,if_neg guard.2,run,h] at nonerror
                exact nonerror
            have postCode := (PanSimp.codeSimAll body s.decClockHOLFinite result post code run bodyNonerror entryRel).2
            have postRel : PanSimp.CodeRel post.code code := by rw [postCode]; exact entryRel
            have postTable : SimpTableSupported post.code factor := by rw [postCode]; exact entryTable
            have postSmall : post.clock < clock := by
              have h := evaluateHOLFiniteState_clock_le s.decClockHOLFinite body
              rw [run] at h
              simp only [decClockHOLFinite] at h
              omega
            have bound := clockIH post.clock postSmall (.while e body) (.while e bodyShape) post postRel postTable loopNonerror rfl
            simpa using bound
          · rw [controlSteps_while,controlSteps_while,evalSame,tested]
            simp only [if_neg guard,Nat.add_zero,Nat.mul_one]
            exact positive
        · rw [controlSteps_while,controlSteps_while,evalSame,tested]; simpa using positive
        · rw [controlSteps_while,controlSteps_while,evalSame,tested]; simpa using positive


/-- Simplifying a call-aware body and its related function table costs at most
one concrete table factor per original source visit, plus the body overhead. -/
theorem callSupported_simp_tableVisits {scope : List VarName} {σ : Type} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) (s : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel s.code code) (factor : Nat) (positive : 1 ≤ factor)
    (table : SimpTableSupported s.code factor)
    (nonerror : (s.evaluateHOLFiniteState (progToHOL program)).1 ≠ some .error) :
    controlSteps (progToHOL (panSimpProg program)) {s with code := code} ≤
      factor * controlSteps (progToHOL program) s + hw (progToHOL (panSimpProg program)) := by
  have tableBound := plainTableBound factor positive (progToHOL program) (callSupportedIn_plain supported)
    s code rel table nonerror
  have reassoc := callSupported_panSimp_controlSteps supported {s with code := code}
  have extra := over_le (({s with code := code} : PanSemStateFiniteExact 64 σ).evaluateHOLFiniteState (progToHOL program)).1
    (hw (progToHOL (panSimpProg program)))
  omega

abbrev SimpEntry := MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL

def simpTableFactor (entries : List SimpEntry) : Nat :=
  1 + entries.foldr (fun entry n => max (hw (panSimpCompileHOL entry.2.2.1)) n) 0

private theorem weight_mem (entries : List SimpEntry) (entry : SimpEntry) (member : entry ∈ entries) :
    hw (panSimpCompileHOL entry.2.2.1) + 1 ≤ simpTableFactor entries := by
  unfold simpTableFactor
  induction entries with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    simp only [List.foldr_cons]
    rcases member with rfl | member
    · have h := Nat.le_max_left (hw (panSimpCompileHOL entry.2.2.1))
        (List.foldr (fun entry n => max (hw (panSimpCompileHOL entry.2.2.1)) n) 0 rest)
      omega
    · have h := ih member
      have h' := Nat.le_max_right (hw (panSimpCompileHOL head.2.2.1))
        (List.foldr (fun entry n => max (hw (panSimpCompileHOL entry.2.2.1)) n) 0 rest)
      omega

private theorem lookupMem {α β : Type} [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (key : α) (value : β) (found : entries.lookup key = some value) :
    (key,value) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons entry rest ih =>
    obtain ⟨name,body⟩ := entry
    by_cases eq : key = name
    · subst name; simp at found; subst body; simp
    · have ne : (key == name) = false := by simp [eq]
      simp only [List.lookup_cons,ne] at found
      exact List.mem_cons_of_mem _ (ih found)

private theorem entry_of_lookup (entries : List SimpEntry) (name : MlS)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (rsh : ShapeHOL)
    (found : lookupCodeHOLFinite (HolFiniteMapExact.empty.updateList entries.reverse).lookup name values = some (body,locals,rsh)) :
    ∃ params, (name,params,body,rsh) ∈ entries := by
  obtain ⟨params,codeFound,_,_,_⟩ := lookupCodeHOLFinite_some_inv _ name values body locals rsh found
  have lookup : entries.lookup name = some (params,body,rsh) := by
    have h := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup entries name
    simp only [FLOOKUP] at h
    rw [HolFiniteMapExact.lookup_updateList] at codeFound
    change FUPDATE_LIST FEMPTY entries.reverse name = _ at codeFound
    rw [h] at codeFound
    exact codeFound
  have member : (name,params,body,rsh) ∈ entries := lookupMem entries name (params,body,rsh) lookup
  exact ⟨params,member⟩

/-- The table factor is computed from the source function entries. -/
theorem simpTableSupported_of_entries (entries : List SimpEntry)
    (shapes : ∀ entry ∈ entries, ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program) :
    SimpTableSupported (HolFiniteMapExact.empty.updateList entries.reverse) (simpTableFactor entries) := by
  intro name values body locals rsh found
  obtain ⟨params,member⟩ := entry_of_lookup entries name values body locals rsh found
  obtain ⟨scope,program,bodyEq,supported⟩ := shapes _ member
  refine ⟨scope,program,bodyEq,supported,?_⟩
  have w := weight_mem entries (name,params,body,rsh) member
  simp only at w
  change body = progToHOL program at bodyEq
  rw [bodyEq,callSupported_panSimp_hol supported] at w
  exact w

/-- Concrete function entries determine both supported and byte-ranged callees. -/
theorem rangedTableSupported_of_entries (entries : List SimpEntry)
    (shapes : ∀ entry ∈ entries, ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program) :
    ∀ name values body locals rsh,
      lookupCodeHOLFinite (HolFiniteMapExact.empty.updateList entries.reverse).lookup name values = some (body,locals,rsh) →
      ∃ scope, ∃ program : Prog (RiscV.Word 64), body = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program := by
  intro name values body locals rsh found
  obtain ⟨params,member⟩ := entry_of_lookup entries name values body locals rsh found
  exact shapes _ member

end SteppedFlapjack.Concrete.SimpVisits
