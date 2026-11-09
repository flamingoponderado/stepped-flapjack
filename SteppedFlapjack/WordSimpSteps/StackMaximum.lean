import SteppedFlapjack.WordSimpSteps.LoopSequence
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}
set_option maxHeartbeats 1000000 in
theorem branch_stackMax {p : WordLangProgHOL (BitVec width)} (hp : Branch p) :
    ∀ s : WordSemStateFiniteExact width C F, (evaluate p s).2.stackMax = s.stackMax := by
  induction hp with
  | seq ha hb iha ihb =>
    intro s
    rw [evaluate, fix_clock_evaluate]
    rcases h : evaluate _ s with ⟨res,t⟩
    have first := iha s
    rw [h] at first
    cases res with
    | none => simp only; exact (ihb t).trans first
    | some r => exact first
  | ite cmp r ri ha hb iha ihb =>
    intro s
    rw [evaluate]
    cases getVar r s <;> cases getVarImm ri s <;> simp only
    split <;> first | rfl | exact iha s | exact ihb s
  | assign _ _ | inst _ | move _ _ | get _ _ | opCurrHeap _ _ _ | set _ _ | store _ _ | skip | tick | ret _ _ | «break» _ | «continue» _ =>
    intro s
    rw [evaluate]
    repeat (first | split)
    all_goals try rfl
    all_goals try (rename_i h; have hh := instConstFull _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.1)
    all_goals try (rename_i h; have hh := memStoreConst _ _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    all_goals split <;> rfl

set_option maxHeartbeats 1000000 in
/-- Branch-bodied loops preserve the recorded maximum stack usage. -/
theorem loop_stackMax (names exits : NumSet) {body : WordLangProgHOL (BitVec width)}
    (bodyMax : ∀ s : WordSemStateFiniteExact width C F, (evaluate body s).2.stackMax = s.stackMax)
    (s : WordSemStateFiniteExact width C F) :
    (evaluate (.loop names body exits) s).2.stackMax = s.stackMax := by
  rw [evaluate]
  cases hc : cutState (names,.ln) s with
  | none => simp
  | some u =>
    have uc : u.clock = s.clock := (cutState_clock_termdep _ _ _ hc).1
    have us : u.stackMax = s.stackMax := by obtain ⟨_,rfl⟩ := cutStateConst _ _ _ hc; rfl
    have hb := bodyMax u
    rcases he : evaluate body u with ⟨res,v⟩
    rw [he] at hb
    have hclock := (evaluate_clock body u res v he).1
    simp only
    rw [fix_clock_evaluate,he]
    simp only
    by_cases hcont : wordSemContLoop res = true
    · simp only [hcont,if_true]
      by_cases hz : v.clock = 0
      · simp [hz,flushState]; exact hb.trans us
      · simp only [hz,wordSemSTOP]
        exact (loop_stackMax names exits bodyMax (decClock v)).trans (hb.trans us)
    · simp only [hcont,Bool.false_eq_true,if_false]
      split
      · split
        · exact hb.trans us
        · rename_i v2 hcut
          have hv2 : v2.stackMax = v.stackMax := by obtain ⟨_,rfl⟩ := cutStateConst _ _ _ hcut; rfl
          exact hv2.trans (hb.trans us)
      · exact hb.trans us
termination_by s.clock
decreasing_by
  simp only [decClock]
  omega


/-- Any call-free sequence of branches and branch-bodied loops leaves the
recorded stack maximum unchanged. -/
theorem loopSequence_stackMax {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    ∀ s : WordSemStateFiniteExact width C F, (evaluate p s).2.stackMax = s.stackMax := by
  induction shape with
  | branch h => exact branch_stackMax h
  | loop names exits h => exact loop_stackMax names exits (branch_stackMax h)
  | nestedLoop names exits h ih => exact loop_stackMax names exits ih
  | conditional cmp r ri ha hb iha ihb =>
    intro s
    rw [evaluate]
    cases getVar r s <;> cases getVarImm ri s <;> simp only
    split <;> first | rfl | exact iha s | exact ihb s
  | seq ha hb iha ihb =>
    intro s
    rw [evaluate, fix_clock_evaluate]
    rcases h : evaluate _ s with ⟨res,t⟩
    have first := iha s
    rw [h] at first
    cases res with
    | none => simp only; exact (ihb t).trans first
    | some r => exact first

end SteppedFlapjack.WordSimpSteps
