import SteppedFlapjack.WordSsaSteps.Permute
import Flapjack.Compiler.Backend.WordAlloc.Proofs.FullSSACorrect

/-! Full SSA correctness and visit bounds for call-free loop sequences. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Full SSA preserves every non-error execution in this fragment and its
result state up to the established SSA relation, with an actual visit bound.
The input domain is the native SSA entry convention. -/
theorem fullSsa_correct_with_steps (count : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : LoopSequence p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (run : evaluate p s = (res,post))
    (nonerror : res ≠ some .error) (domain : sptDomain s.locals = (fun key => key ∈ evenList count)) :
    ∃ targetPost,
      evaluate (fullSsaCcTrans count p) s = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel post targetPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => post.locals = targetPost.locals) ∧
      steps (fullSsaCcTrans count p) s ≤ sizeOf (fullSsaCcTrans count p) * (s.clock+1) := by
  obtain ⟨perm,correct⟩ := fullSsaCcTransCorrect p s count domain
  have permRun := loopSequence_withPermute shape s perm
  rw [run] at permRun
  simp only at permRun
  have permNonerror : (evaluate p {s with permute := perm}).1 ≠ some .error := by rw [permRun]; exact nonerror
  dsimp only at correct
  rw [if_neg permNonerror,permRun] at correct
  rcases targetRun : evaluate (fullSsaCcTrans count p) s with ⟨targetResult,targetPost⟩
  simp only [targetRun] at correct
  refine ⟨targetPost,?_,?_,?_,fullSsa_clock_bound count shape s⟩
  · exact congrArg (fun r => (r,targetPost)) correct.1.symm
  · simpa only [Flapjack.WordAlloc.wordStateEqRel] using correct.2.1
  · cases res with
    | none => trivial
    | some r => cases r <;> exact correct.2.2

end SteppedFlapjack.WordSsaSteps
