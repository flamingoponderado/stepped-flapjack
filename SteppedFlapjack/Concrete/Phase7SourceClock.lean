import SteppedFlapjack.Concrete.Phase7Compiler
import Flapjack.Pancake.Semantics.PanSem.ClockTimeout

/-! Finite source clock monotonicity for observational semantics. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Increasing the source clock after a non-timeout run preserves its result
and all fields other than the remaining clock. -/
theorem source_add_clock {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s t : PanSemStateFiniteExact width σ)
    (q : Option (PanSemResultExact width)) (extra : Nat)
    (run : evaluateHOLFiniteState s p = (q,t)) (notTimeout : q ≠ some .timeOut) :
    evaluateHOLFiniteState {s with clock := s.clock + extra} p = (q,{t with clock := t.clock + extra}) := by
  classical
  let hm : DecidablePred s.memaddrs := fun a => Classical.propDecidable (s.memaddrs a)
  let hs : DecidablePred s.shMemaddrs := fun a => Classical.propDecidable (s.shMemaddrs a)
  let low : FiniteEvalContext width σ := ⟨s,hm,hs⟩
  let high : FiniteEvalContext width σ := ⟨{s with clock := s.clock + extra},hm,hs⟩
  obtain ⟨x,hx⟩ := evalPanSemRecursiveCallFiniteContext_total p low
  obtain ⟨y,hy⟩ := evalPanSemRecursiveCallFiniteContext_total p high
  have heval : evaluateHOLFiniteStateWithDeciders s p (h := hm) (hshared := hs) = (q,t) := by
    rw [← evaluateHOLFiniteState_eq_withDeciders (state := s) (hmem := hm) (hshared := hs) (program := p)]
    exact run
  simp only [evaluateHOLFiniteStateWithDeciders,low,hx] at heval
  have xq : x.1 = q := congrArg Prod.fst heval
  have xt : x.2.state = t := congrArg Prod.snd heval
  have hlow : evalPanSemRecursiveCallContextHOLExact p low.toExact = some (x.1,x.2.toExact) := by
    have h := evalPanSemRecursiveCallFiniteContext_projection p low
    simp only [hx,Option.map_some] at h
    exact h.symm
  have hhigh : evalPanSemRecursiveCallContextHOLExact p high.toExact = some (y.1,y.2.toExact) := by
    have h := evalPanSemRecursiveCallFiniteContext_projection p high
    simp only [hy,Option.map_some] at h
    exact h.symm
  have stateEq : (ctxAddClock low.toExact extra).state = high.toExact.state := rfl
  have hhigh' : evalPanSemRecursiveCallContextHOLExact p (ctxAddClock low.toExact extra) = some (y.1,y.2.toExact) :=
    (eval_context_state p (ctxAddClock low.toExact extra) high.toExact stateEq).trans hhigh
  have mono := (eval_add_clock_mono_aux p low.toExact extra _ _ hlow hhigh').2 (by simpa [xq] using notTimeout)
  have yq : y.1 = q := ((Prod.mk.inj mono).1).trans xq
  have ystate : y.2.state = {t with clock := t.clock + extra} := by
    apply PanSemStateFiniteExact.toExact_injective
    have h := congrArg PanSemExactEvalContext.state (Prod.mk.inj mono).2
    change y.2.state.toExact = stateAddClock x.2.state.toExact extra at h
    rw [xt] at h
    exact h
  rw [evaluateHOLFiniteState_eq_withDeciders (state := {s with clock := s.clock + extra})
    (hmem := hm) (hshared := hs) (program := p)]
  simp only [evaluateHOLFiniteStateWithDeciders, high, hy, yq, ystate]
/-- A successful clocked source entry determines its unclocked observation. -/
theorem source_semantics_of_return {width : Nat} {σ : Type} [NeZero width]
    (s t : PanSemStateFiniteExact width σ) (start : MlS) (clock : Nat) (value : ValueHOL width)
    (run : evaluateHOLFiniteState {s with clock := clock} (.call none start []) = (some (.returned value),t)) :
    semantics s start = .terminate .success t.ffi.ioEvents := by
  classical
  let entry : ProgHOL width := .call none start []
  have compare (k : Nat) :
      let r := evaluateHOLFiniteState {s with clock := k} entry
      r.1 = some .timeOut ∨ (r.1 = some (.returned value) ∧ r.2.ffi.ioEvents = t.ffi.ioEvents) := by
    let out := evaluateHOLFiniteState {s with clock := k} entry
    by_cases smaller : k ≤ clock
    · by_cases timeout : out.1 = some .timeOut
      · exact Or.inl timeout
      · have low : evaluateHOLFiniteState {s with clock := k} entry = (out.1,out.2) := Prod.mk.eta.symm
        have high := source_add_clock entry {s with clock := k} out.2 out.1 (clock-k) low timeout
        have high' : evaluateHOLFiniteState {s with clock := clock} entry =
            (out.1,{out.2 with clock := out.2.clock + (clock-k)}) := by
          simpa only [show k + (clock-k) = clock by omega] using high
        have eq := high'.symm.trans run
        have res : out.1 = some (.returned value) := (Prod.mk.inj eq).1
        have events : out.2.ffi.ioEvents = t.ffi.ioEvents := by
          have st := (Prod.mk.inj eq).2
          simpa only using congrArg (fun state : PanSemStateFiniteExact width σ => state.ffi.ioEvents) st
        exact Or.inr ⟨res,events⟩
    · have high := source_add_clock entry {s with clock := clock} t (some (.returned value)) (k-clock) run (by simp)
      have high' : evaluateHOLFiniteState {s with clock := k} entry =
          (some (.returned value),{t with clock := t.clock + (k-clock)}) := by
        simpa only [show clock + (k-clock) = k by omega] using high
      exact Or.inr ⟨congrArg Prod.fst high',congrArg (fun x => x.2.ffi.ioEvents) high'⟩
  have noFail : ¬ ∃ k, (match (evaluateHOLFiniteState {s with clock := k} entry).1 with
      | some .timeOut => False | some (.finalFfi _) => False | some (.returned _) => False | _ => True) := by
    intro ⟨k,bad⟩
    rcases compare k with timed | ⟨returned,_⟩
    · simp [timed] at bad
    · simp [returned] at bad
  have chosen : holOptionSome (fun res => ∃ k st r outcome,
      evaluateHOLFiniteState {s with clock := k} entry = (r,st) ∧
      (match r with | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
                    | some (.returned _) => outcome = HolOutcome.success | _ => False) ∧
      res = HolBehaviour.terminate outcome st.ffi.ioEvents) = some (.terminate .success t.ffi.ioEvents) := by
    apply HolLList.holOptionSome_eq_some
    · exact ⟨clock,t,some (.returned value),.success,run,rfl,rfl⟩
    · intro result h
      obtain ⟨k,st,r,outcome,hr,hout,heq⟩ := h
      rw [heq]
      rcases compare k with timed | ⟨returned,events⟩
      · rw [hr] at timed
        simp at timed
        subst r
        simp at hout
      · rw [hr] at returned events
        simp only at returned events
        subst r
        simp only at hout
        subst outcome
        simpa using congrArg (HolBehaviour.terminate .success) events
  dsimp only [entry] at chosen
  unfold semantics
  change (if (∃ k, (match (evaluateHOLFiniteState {s with clock := k} entry).1 with
      | some .timeOut => False | some (.finalFfi _) => False | some (.returned _) => False | _ => True))
    then HolBehaviour.fail else _) = _
  rw [if_neg noFail]
  change (match holOptionSome (fun res => ∃ k st r outcome,
      evaluateHOLFiniteState {s with clock := k} (.call none start []) = (r,st) ∧
      (match r with | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
                    | some (.returned _) => outcome = HolOutcome.success | _ => False) ∧
      res = HolBehaviour.terminate outcome st.ffi.ioEvents) with
    | some res => res | none => _) = _
  rw [chosen]
end SteppedFlapjack.Concrete
