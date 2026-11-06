import SteppedFlapjack.WordSimpSteps.RiscV

/-! WordSimp on the tick/loop/tick shape produced by Loop-to-Word. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

/-- The actual WordSimp result for Loop-to-Word's loop wrapper. -/
theorem compileExp_tick_loop (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width)) :
    compileExp (.seq .tick (.seq (.loop names body exits) .tick)) =
      .seq (.seq .tick (.loop names (compileExp body) exits)) .tick := by
  simp only [Compiler.Backend.WordSimp.compileExp, Compiler.Backend.WordSimp.seqAssoc,
    Compiler.Backend.WordSimp.smartSeqHOL, constFp, constFpLoop, simpDuplicateIf,
    tryIfHoist1, destIf, pushOutIf, pushOutIfAux]

/-- Wrapping a bounded semantics-preserving loop between ticks retains a
source-relative visit bound, including clock exhaustion and early results. -/
theorem tick_loop_steps (names exits : Spt Unit) {body : WordLangProgHOL (BitVec width)}
    (shape : Branch body) (s : WordSemStateFiniteExact width C F) (gc : gcFunConstOk s.gcFun) :
    steps (compileExp (.seq .tick (.seq (.loop names body exits) .tick))) s ≤
      (3 + sizeOf (compileExp body)) * steps (.seq .tick (.seq (.loop names body exits) .tick)) s := by
  rw [compileExp_tick_loop, steps_seq, steps_seq, steps_seq, evaluate_seq_eq]
  rcases tickRun : evaluate (.tick : WordLangProgHOL (BitVec width)) s with ⟨tickResult, mid⟩
  cases tickResult with
  | some r => simp only; have positive := steps_pos (.tick : WordLangProgHOL (BitVec width)) s; nlinarith
  | none =>
    simp only
    have constants := evaluate_consts (.tick : WordLangProgHOL (BitVec width)) s none mid tickRun
    have midGc : gcFunConstOk mid.gcFun := by rw [← constants.1]; exact gc
    have loopBound := compileExp_loop_branch_correct names exits shape mid midGc
    rw [steps_seq]
    rw [compileExp_loop] at loopBound
    rw [loopBound.1]
    rcases loopRun : evaluate (.loop names body exits) mid with ⟨r, post⟩
    cases r <;> simp only <;> have pos := steps_pos (.tick : WordLangProgHOL (BitVec width)) s <;> nlinarith

end SteppedFlapjack.WordSimpSteps
