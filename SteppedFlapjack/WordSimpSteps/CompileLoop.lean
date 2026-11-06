import SteppedFlapjack.WordSimpSteps.CompileBranch

/-! Complete WordSimp bounds for loops with branch bodies. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

/-- The real pass recurses into a loop body with a fresh constant map. -/
theorem compileExp_loop (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width)) :
    compileExp (.loop names body exits) = .loop names (compileExp body) exits := by
  rfl

/-- The complete WordSimp pass on a loop with a supported branching body has
a syntax-dependent visit bound and preserves evaluation. -/
theorem compileExp_loop_branch_correct (names exits : Spt Unit)
    {body : WordLangProgHOL (BitVec width)} (shape : Branch body)
    (source : WordSemStateFiniteExact width C F) (gc : gcFunConstOk source.gcFun) :
    evaluate (compileExp (.loop names body exits)) source = evaluate (.loop names body exits) source ∧
    steps (compileExp (.loop names body exits)) source ≤
      (1 + sizeOf (compileExp body)) * steps (.loop names body exits) source := by
  rw [compileExp_loop]
  constructor
  · apply evaluate_Loop_body_cong_gc (fun f => gcFunConstOk f) source names body (compileExp body) exits
    · intro s good; exact (compileExp_branch_correct shape s good).1
    · exact gc
  · induction hc : source.clock using Nat.strongRecOn generalizing source with
    | _ clock ih =>
      rw [steps_loop, steps_loop]
      rcases cut : cutState (names,.ln) source with _ | entry
      · simp only
        omega
      · simp only
        obtain ⟨loc, entryEq⟩ := cutStateConst _ _ _ cut
        have gcEntry : gcFunConstOk entry.gcFun := by rw [entryEq]; exact gc
        have bound := compileExp_branch_steps shape entry
        rw [(compileExp_branch_correct shape entry gcEntry).1]
        rcases run : evaluate body entry with ⟨result, post⟩
        by_cases cont : wordSemContLoop result ∧ post.clock ≠ 0
        · have cutClock := cutState_clock_termdep _ _ _ cut
          have runClock := evaluate_clock body entry result post run
          have preserved := evaluate_consts body entry result post run
          have nextGc : gcFunConstOk (decClock post).gcFun := by
            change gcFunConstOk post.gcFun
            rw [← preserved.1]
            exact gcEntry
          have smaller : (decClock post).clock < source.clock := by simp only [decClock]; omega
          have rest := ih _ (by simpa [hc] using smaller) (decClock post) nextGc rfl
          simp only [cont.1, true_and, if_pos cont.2]
          have positive := steps_pos body entry
          nlinarith
        · simp only [cont, if_false]
          nlinarith

end SteppedFlapjack.WordSimpSteps
