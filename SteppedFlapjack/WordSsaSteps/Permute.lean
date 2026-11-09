import SteppedFlapjack.WordSsaSteps.Selection
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap

/-! Permutation independence for the call-free SSA input fragment. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Loop-free branches do not inspect or change the permutation oracle. -/
theorem branch_withPermute {p : WordLangProgHOL (BitVec width)} (shape : Branch p)
    (s : WordSemStateFiniteExact width C F) (perm : Nat → Nat → Nat) :
    evaluate p {s with permute := perm} =
      ((evaluate p s).1,{(evaluate p s).2 with permute := perm}) := by
  induction shape generalizing s with
  | seq ha hb iha ihb =>
    rw [evaluate_seq_eq,evaluate_seq_eq,iha]
    rcases run : evaluate _ s with ⟨res,post⟩
    cases res with
    | none => simpa only using ihb post
    | some r => rfl
  | ite cmp r ri ha hb iha ihb =>
    have hv : WordSemStateFiniteExact.getVar r {s with permute := perm} = WordSemStateFiniteExact.getVar r s := rfl
    have hi : WordSemStateFiniteExact.getVarImm ri {s with permute := perm} = WordSemStateFiniteExact.getVarImm ri s := by cases ri <;> rfl
    rw [evaluate,evaluate,hv,hi]
    cases hx : WordSemStateFiniteExact.getVar r s <;> cases hy : WordSemStateFiniteExact.getVarImm ri s <;> simp only
    case some.some x y =>
      cases hv : wordSemWordCmp cmp x y with
      | none => rfl
      | some v => cases v <;> first | exact ihb s | exact iha s
  | assign _ _ | inst _ | move _ _ | get _ _ | opCurrHeap _ _ _ | set _ _ | store _ _ | skip | tick | ret _ _ | «break» _ | «continue» _ =>
    exact evaluate_withPermute_const s perm _ rfl

/-- A loop with a permutation-independent body is independent of the permutation oracle. -/
theorem loop_withPermute (names exits : Spt Unit) {body : WordLangProgHOL (BitVec width)}
    (perm : Nat → Nat → Nat)
    (bodyPerm : ∀ s : WordSemStateFiniteExact width C F, evaluate body {s with permute := perm} =
      ((evaluate body s).1,{(evaluate body s).2 with permute := perm}))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.loop names body exits) {s with permute := perm} =
      ((evaluate (.loop names body exits) s).1,{(evaluate (.loop names body exits) s).2 with permute := perm}) := by
  induction hc : s.clock using Nat.strongRecOn generalizing s with
  | _ clock ih =>
    have loopEq := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [← hc]
    rw [loopEq,loopEq,cutState_withPermute s perm (names,.ln)]
    rcases cut : cutState (names,.ln) s with _ | entry
    · rfl
    · simp only [Option.map_some]
      have cutClock := cutState_clock_termdep _ _ _ cut
      rcases run : evaluate body entry with ⟨res,post⟩
      have permRun := bodyPerm entry
      rw [run] at permRun
      simp only at permRun
      rw [permRun]
      by_cases cont : wordSemContLoop res = true
      · by_cases zero : post.clock = 0
        · simp [cont,zero,flushState]
        · have clockLe := (evaluate_clock body entry res post run).1
          have smaller : (decClock post).clock < clock := by simp only [decClock]; omega
          have rest := ih _ smaller (decClock post) rfl
          simp only [cont,if_true,zero,if_false,wordSemSTOP]
          simpa only [decClock] using rest
      · simp only [cont,Bool.false_eq_true,if_false]
        cases res with
        | none => simp [wordSemContLoop] at cont
        | some r =>
          cases r with
          | «break» n =>
            cases n with
            | zero =>
              simp only
              rw [cutState_withPermute]
              cases cutState (exits,.ln) post <;> rfl
            | succ n => rfl
          | _ => rfl

/-- Recursive supported programs are independent of permutations. -/
theorem loopSequence_withPermute {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) (perm : Nat → Nat → Nat) :
    evaluate p {s with permute := perm} =
      ((evaluate p s).1,{(evaluate p s).2 with permute := perm}) := by
  induction shape generalizing s with
  | branch h => exact branch_withPermute h s perm
  | loop names exits h => exact loop_withPermute names exits perm (fun s => branch_withPermute h s perm) s
  | nestedLoop names exits h ih => exact loop_withPermute names exits perm ih s
  | conditional cmp r ri ha hb iha ihb =>
    have hv : WordSemStateFiniteExact.getVar r {s with permute := perm} = WordSemStateFiniteExact.getVar r s := rfl
    have hi : WordSemStateFiniteExact.getVarImm ri {s with permute := perm} = WordSemStateFiniteExact.getVarImm ri s := by cases ri <;> rfl
    rw [evaluate,evaluate,hv,hi]
    cases hx : WordSemStateFiniteExact.getVar r s <;> cases hy : WordSemStateFiniteExact.getVarImm ri s <;> simp only
    case some.some x y =>
      cases hv : wordSemWordCmp cmp x y with
      | none => rfl
      | some v => cases v <;> first | exact ihb s | exact iha s
  | seq ha hb iha ihb =>
    rw [evaluate_seq_eq,evaluate_seq_eq,iha]
    rcases run : evaluate _ s with ⟨res,post⟩
    cases res with
    | none => simpa only using ihb post
    | some r => rfl

end SteppedFlapjack.WordSsaSteps
