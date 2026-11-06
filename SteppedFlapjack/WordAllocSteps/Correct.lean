import SteppedFlapjack.WordDeadSteps.Second
import Flapjack.Compiler.Backend.WordAlloc.Proofs.WordAllocCorrect

/-! Register allocation preserves the bounded call-free Word fragment. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordSteps
open Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

theorem colour_branch (f : Nat → Nat) {p : WordLangProgHOL (BitVec width)} (h : Branch p) :
    Branch (applyColour f p) := by
  induction h with
  | assign _ _ => exact .assign _ _
  | inst _ => exact .inst _
  | move _ _ => exact .move _ _
  | get _ _ => exact .get _ _
  | opCurrHeap _ _ _ => exact .opCurrHeap _ _ _
  | set _ _ => exact .set _ _
  | store _ _ => exact .store _ _
  | skip => exact .skip
  | tick => exact .tick
  | ret _ _ => exact .ret _ _
  | «break» _ => exact .break _
  | «continue» _ => exact .continue _
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | ite _ _ _ _ _ ih1 ih2 => exact .ite _ _ _ ih1 ih2

theorem colour_loopSequence (f : Nat → Nat) {p : WordLangProgHOL (BitVec width)}
    (h : LoopSequence p) : LoopSequence (applyColour f p) := by
  induction h with
  | branch h => exact .branch (colour_branch f h)
  | loop _ _ h => exact .loop _ _ (colour_branch f h)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2

theorem wordAlloc_loopSequence (fc : Nat) (ac : AsmConfigExact width) (alg k : Nat)
    {p : WordLangProgHOL (BitVec width)} (col : Option (Spt Nat)) (h : LoopSequence p) :
    LoopSequence (wordAlloc fc ac alg k p col) := by
  simp only [wordAlloc]
  cases ho : oracleColourOk k col (getClashTree p []) p (getForced ac p []) with
  | none =>
    simp only
    cases hh : getHeuristics alg fc p with
    | mk moves costs =>
      simp only
      cases hs : selectRegAlloc alg costs k moves (getClashTree p []) (getForced ac p []) (getStackOnly p) with
      | success colour => exact colour_loopSequence _ h
      | failure failure => exact h
  | some coloured =>
    simp only
    cases col with
    | none => simp [oracleColourOk] at ho
    | some c =>
      simp only [oracleColourOk] at ho
      split at ho
      · split at ho
        · simp only [Option.some.injEq] at ho
          subst coloured
          exact colour_loopSequence _ h
        · cases ho
      · cases ho

/-- The actual allocator preserves non-error executions and admits a syntax and
clock bound for its evaluator visits, including all allocator branches. -/
theorem wordAlloc_correct_with_steps (fc : Nat) (ac : AsmConfigExact width) (alg k : Nat)
    {p : WordLangProgHOL (BitVec width)} (col : Option (Spt Nat)) (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error)
    (even : Flapjack.Compiler.Backend.WordAlloc.Proofs.evenStartingLocals s.locals)
    (cutsets : wfCutsets p) :
    ∃ targetPost,
      evaluate (wordAlloc fc ac alg k p col) s = (res,targetPost) ∧
      wordStateEqRel post targetPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => post.locals = targetPost.locals) ∧
      steps (wordAlloc fc ac alg k p col) s ≤ sizeOf (wordAlloc fc ac alg k p col) * (s.clock+1) := by
  obtain ⟨perm,correct⟩ := wordAllocCorrect fc ac alg p k col s ⟨even,cutsets⟩
  have permRun := loopSequence_withPermute shape s perm
  rw [run] at permRun
  simp only at permRun
  have permNonerror : (evaluate p {s with permute := perm}).1 ≠ some .error := by rw [permRun]; exact nonerror
  dsimp only at correct
  rw [if_neg permNonerror,permRun] at correct
  rcases targetRun : evaluate (wordAlloc fc ac alg k p col) s with ⟨targetResult,targetPost⟩
  simp only [targetRun] at correct
  refine ⟨targetPost,?_,?_,?_,loopSequence_clock_bound (wordAlloc_loopSequence fc ac alg k col shape) s⟩
  · exact congrArg (fun r => (r,targetPost)) correct.1.symm
  · simpa only [wordStateEqRel] using correct.2.1
  · cases res with
    | none => trivial
    | some r => cases r <;> exact correct.2.2

end SteppedFlapjack.WordAllocSteps
