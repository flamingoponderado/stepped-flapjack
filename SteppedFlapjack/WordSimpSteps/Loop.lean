import SteppedFlapjack.WordSimpSteps.Straight

/-! Lifting WordSimp body bounds through loops. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp SteppedFlapjack.WordInstSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A semantics-preserving transformation with a uniform body visit bound
induces a loop visit bound, including cut failures and early exits. -/
theorem loop_body_steps_bound (names exits : Spt Unit)
    (body body' : WordLangProgHOL (BitVec width)) (factor : Nat)
    (same : ∀ s : WordSemStateFiniteExact width C F, evaluate body' s = evaluate body s)
    (bound : ∀ s : WordSemStateFiniteExact width C F, steps body' s ≤ factor * steps body s)
    (source : WordSemStateFiniteExact width C F) :
    steps (.loop names body' exits) source ≤ (1 + factor) * steps (.loop names body exits) source := by
  induction hc : source.clock using Nat.strongRecOn generalizing source with
  | _ clock ih =>
    rw [steps_loop, steps_loop]
    rcases cut : cutState (names,.ln) source with _ | entry
    · simp only
      omega
    · simp only
      have smallBody := bound entry
      rw [same entry]
      rcases run : evaluate body entry with ⟨result, post⟩
      by_cases cont : wordSemContLoop result ∧ post.clock ≠ 0
      · have cutClock := cutState_clock_termdep _ _ _ cut
        have runClock := evaluate_clock body entry result post run
        have smaller : (decClock post).clock < source.clock := by
          simp only [decClock]
          omega
        have rest := ih _ (by simpa [hc] using smaller) (decClock post) rfl
        simp only [cont.1, true_and, if_pos cont.2]
        have positive := steps_pos body entry
        nlinarith
      · simp only [cont, if_false]
        nlinarith

/-- WordSimp's sequence normalizer on a loop with a straight body preserves
evaluation and bounds the loop's actual visits relative to the original. -/
theorem seqAssoc_loop_straight (names exits : Spt Unit)
    {body : WordLangProgHOL (BitVec width)} (shape : Straight body)
    (source : WordSemStateFiniteExact width C F) :
    evaluate (seqAssoc .skip (.loop names body exits)) source = evaluate (.loop names body exits) source ∧
    steps (seqAssoc .skip (.loop names body exits)) source ≤
      (1 + sizeOf (seqAssoc .skip body)) * steps (.loop names body exits) source := by
  constructor
  · exact evaluate_Seq_assoc _ source
  · change steps (.loop names (seqAssoc .skip body) exits) source ≤ _
    apply loop_body_steps_bound names exits body (seqAssoc .skip body)
    · intro s; exact evaluate_Seq_assoc body s
    · intro s; exact seqAssoc_straight_steps shape s

/-- The complete WordSimp pass normalizes the straight loop body without
changing the surrounding loop. -/
theorem compileExp_loop_straight (names exits : Spt Unit)
    {body : WordLangProgHOL (BitVec width)} (shape : Straight body) :
    compileExp (.loop names body exits) = .loop names (seqAssoc .skip body) exits := by
  have bodyShape := seqAssoc_straight shape Straight.skip
  simp only [Compiler.Backend.WordSimp.compileExp, Compiler.Backend.WordSimp.seqAssoc, Compiler.Backend.WordSimp.smartSeqHOL, constFp,
    constFpLoop, constFpLoop_straight bodyShape, simpDuplicateIf,
    simpDuplicateIf_straight bodyShape, pushOutIf, pushOutIfAux,
    pushOutIfAux_straight bodyShape]

/-- A complete WordSimp execution of a loop with a straight body preserves the
Word result and has a syntax-dependent bound on visits. -/
theorem compileExp_loop_straight_correct (names exits : Spt Unit)
    {body : WordLangProgHOL (BitVec width)} (shape : Straight body)
    (source : WordSemStateFiniteExact width C F) :
    evaluate (compileExp (.loop names body exits)) source = evaluate (.loop names body exits) source ∧
    steps (compileExp (.loop names body exits)) source ≤
      (1 + sizeOf (seqAssoc .skip body)) * steps (.loop names body exits) source := by
  rw [compileExp_loop_straight names exits shape]
  constructor
  · exact evaluate_Loop_body_cong source names body _ exits (fun s => evaluate_Seq_assoc body s)
  · exact loop_body_steps_bound names exits body (seqAssoc .skip body) _
      (fun s => evaluate_Seq_assoc body s) (seqAssoc_straight_steps shape) source

end SteppedFlapjack.WordSimpSteps
