import SteppedFlapjack.WordSimpSteps.LoopSequenceClock
import SteppedFlapjack.WordSimpSteps.ClockConsumption

/-! Source-step bounds for WordSimp on sequences with loops. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

theorem branch_clockProgram {p : WordLangProgHOL (BitVec width)} (hp : Branch p) : clockProgram p = true := by
  induction hp <;> simp_all [clockProgram,wordProgClockConst]

theorem loopSequence_clockProgram {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) : clockProgram p = true := by
  induction hp with
  | branch hp => exact branch_clockProgram hp
  | loop names exits hb => simpa [clockProgram] using branch_clockProgram hb
  | seq ha hb iha ihb => simp [clockProgram,iha,ihb]
  | nestedLoop names exits h ih => simpa [clockProgram] using ih
  | conditional cmp r ri ha hb iha ihb => simp [clockProgram,iha,ihb]

/-- Replay a non-timeout run with any clock bounding its visits, including
unselected expression assignments and stores. -/
theorem loopSequence_normalized_run {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (notTimeout : res ≠ some .timeOut) (sourceBound : steps p s ≤ limit) :
    evaluate p {s with clock := limit} = (res,{post with clock := limit - (s.clock-post.clock)}) := by
  have cost := clockProgram_consumed_le_steps p s (loopSequence_clockProgram shape)
  rw [run] at cost
  have le : s.clock - post.clock ≤ limit := Nat.le_trans cost sourceBound
  have reduced := evaluate_dec_clock p s res post run
  have extended := evaluate_add_clock (limit - (s.clock-post.clock)) p
    {s with clock := s.clock-post.clock} res {post with clock := 0} ⟨reduced,notTimeout⟩
  have eqn : s.clock-post.clock + (limit-(s.clock-post.clock)) = limit := by omega
  simpa only [eqn,Nat.zero_add] using extended

/-- The complete WordSimp pass preserves a normalized execution of a sequence
with recursive control flow, and its actual visits are bounded in terms of the
original source visit bound. -/
theorem loopSequence_wordSimp_normalized {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun) :
    evaluate (compileExp p) {s with clock := limit} = (res,{post with clock := limit-(s.clock-post.clock)}) ∧
    steps (compileExp p) {s with clock := limit} ≤ sizeOf (compileExp p) * (limit+1) := by
  have normalized := loopSequence_normalized_run shape s post res limit run notTimeout sourceBound
  have good : gcFunConstOk ({s with clock := limit} : WordSemStateFiniteExact width C F).gcFun := gc
  have semantics := (compileExp_loopSequence_correct shape {s with clock := limit} good).2
  exact ⟨semantics.trans normalized,loopSequence_clock_bound (compileExp_loopSequence shape) {s with clock := limit}⟩

end SteppedFlapjack.WordSimpSteps
