import SteppedFlapjack.Concrete.CountdownLiteral
import Flapjack.Compiler.Backend.WordToWord.FastCompile
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps
namespace SteppedFlapjack.Concrete
/-- Callee in the generated unoptimized countdown Word table. -/
def countdownWordCallee (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
  match countdownWordLiteral x 0 with
  | [_, (_,_,p)] => p
  | _ => .skip
/-- Countdown callee after the Word simplifier. -/
def countdownSimplifiedWord (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
  .seq (.seq (.seq (.seq (.seq (.assign 2 (.const x)) .tick)
    (.loop (.bs (.ls ()) () .ln)
      (.seq (.seq (.assign 4 (.var 2))
        (.ite .notEqual 4 (.imm 0)
          (.seq (.seq (.assign 4 (.op .sub [.var 2,.const 1])) (.assign 2 (.var 4))) (.continue 0))
          (.break 0))) .tick) (.ls ()))) .tick) (.assign 4 (.const 0))) (.return 0 [4])
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem countdown_wordSimp_literal (x : BitVec 64) : WordSimp.compileExp (countdownWordCallee x) = countdownSimplifiedWord x := by
  unfold countdownWordCallee countdownWordLiteral countdownSimplifiedWord
  simp only [WordSimp.compileExp, WordSimp.seqAssoc, WordSimp.smartSeqHOL, WordSimp.constFp, WordSimp.constFpLoop,
    WordSimp.constFpExp, WordSimp.simpDuplicateIf, WordSimp.pushOutIf]
  with_unfolding_all rfl

/-- Countdown callee after RISC-V instruction selection. -/
def countdownSelectedWord (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
  .seq (.seq (.seq (.seq (.seq (.inst (.const 2 x)) .tick)
    (.loop (.bs (.ls ()) () .ln)
      (.seq (.seq (.move 0 [(4,2)])
        (.ite .notEqual 4 (.imm 0)
          (.seq (.seq (.seq (.move 0 [(5,2)]) (.inst (.arith (.binop .add 4 5 (.imm (-1)))))) (.move 0 [(2,4)])) (.continue 0))
          (.break 0))) .tick) (.ls ()))) .tick) (.inst (.const 4 0))) (.return 0 [4])
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem countdown_instruction_literal (x : BitVec 64) : WordInst.instSelectExecutable riscvConfig (maxVarHOL (countdownSimplifiedWord x)+1) (countdownSimplifiedWord x) = countdownSelectedWord x := by
  unfold countdownSimplifiedWord countdownSelectedWord
  simp only [maxVarHOL,maxVarExpHOL,WordInst.instSelectExecutable,WordInst.ExecutablePullExp.pullExpExecutable,WordInst.flattenExp,WordInst.instSelectExp]
  with_unfolding_all rfl

end SteppedFlapjack.Concrete
