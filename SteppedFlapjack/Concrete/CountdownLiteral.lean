import SteppedFlapjack.Concrete.CountdownWordSpan
import SteppedFlapjack.PanToCrepSteps.CountdownWordLiteral
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
namespace SteppedFlapjack.Concrete
/-- Raw generated Loop callee, before liveness. -/
def countdownRawLoop (x : BitVec 64) :=
 let p := naturalCountdownCrepBody x
 let c := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (twoPrograms (ofString "main") (entryName (naturalCountdownHOL 0)) p)) 0
 compileHOLExact c .ln p
/-- The parameterized raw Loop literal. -/
def countdownRawLoopLiteral (x : BitVec 64) : HolLoopProg 64 :=
  .seq .skip (.seq (.assign 1 (.const x))
    (.seq (.loop (.bn .ln (.ls ()))
      (.seq (.assign 2 (.var 1)) (.seq
        (.ite .notEqual 2 (.imm 0)
          (.seq (.seq .skip (.seq (.assign 2 (.op .sub [.var 1,.const 1]))
            (.seq (.seq (.assign 1 (.var 2)) .skip) .skip))) (.continue 0))
          (.break 0) (.bn .ln (.ls ()))) .skip)) (.bn .ln (.ls ())))
      (.seq (.assign 2 (.const 0)) (.seq (.return [2]) .skip))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem countdownRawLoop_eq (x : BitVec 64) : countdownRawLoop x = countdownRawLoopLiteral x := by
  unfold countdownRawLoop countdownRawLoopLiteral naturalCountdownCrepBody
  simp only [compileHOLExact, compileExpHOLExact, compileExpsHOLExact]
  with_unfolding_all rfl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem countdownRawLoop_opt_eq (x : BitVec 64) : optimiseScalar (countdownRawLoopLiteral x) =
    ((countdownLoopLiteral x 0).get ⟨1, by simp [countdownLoopLiteral]⟩).2.2 := by
  unfold countdownRawLoopLiteral countdownLoopLiteral
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem countdownTwoLoops_literal (n : Nat) : twoLoopPrograms riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n) = countdownLoopLiteral (BitVec.ofNat 64 n) 0 := by
  have nameEq : entryName (naturalCountdownHOL n) = entryName (naturalCountdownHOL 0) := by rfl
  rw [nameEq, twoLoops_exact _ _ _ _ (by
    simpa [← nameEq] using Ne.symm (entryName_fresh (naturalCountdownHOL n)))]
  have h : twoCallee riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL 0))
      (phase3CountdownCrepBody n) = ((countdownLoopLiteral (BitVec.ofNat 64 n) 0).get ⟨1, by simp [countdownLoopLiteral]⟩).2.2 := by
    change optimiseScalar (countdownRawLoop (BitVec.ofNat 64 n)) = _
    rw [countdownRawLoop_eq, countdownRawLoop_opt_eq]
  rw [h]
  rfl

/-- The Phase 2 compiler emits this Word literal for every input word. -/
theorem countdownWordPrograms_literal (n : Nat) :
    countdownWordPrograms n = countdownWordLiteral (BitVec.ofNat 64 n) 0 := by
  unfold countdownWordPrograms countdownCrepCode
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (naturalCountdown_scalar n), countdownTwoLoops_literal,
    countdownLoopLiteral_toWord]

end SteppedFlapjack.Concrete
