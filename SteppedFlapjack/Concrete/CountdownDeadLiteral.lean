import SteppedFlapjack.Concrete.CountdownSsaLiteral
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete
namespace SteppedFlapjack.Concrete

/-- Countdown SSA output after removing dead instructions. -/
def countdownDeadWord (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(9, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 13 x))
            (Flapjack.WordLangProgHOL.tick))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.move 0 [(17, 9), (21, 13)])
            (Flapjack.WordLangProgHOL.loop
              (Flapjack.Spt.bn
                (Flapjack.Spt.ln)
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ()))
                    (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                  (Flapjack.Spt.ln)))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.move 0 [(25, 21)])
                    (Flapjack.WordLangProgHOL.ite
                      (Flapjack.Cmp.notEqual)
                      25
                      (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.seq
                              (Flapjack.WordLangProgHOL.move 0 [(29, 25)])
                              (Flapjack.WordLangProgHOL.inst
                                (Flapjack.WordLangInst.arith
                                  (Flapjack.WordLangArith.binop
                                    (Flapjack.BinOp.add)
                                    33
                                    29
                                    (Flapjack.WordRegImm.imm 0xffffffffffffffff#64)))))
                            (Flapjack.WordLangProgHOL.move 0 [(37, 33)]))
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.move 1 [(21, 37)])
                            (Flapjack.WordLangProgHOL.continue 0)))
                        (Flapjack.WordLangProgHOL.move 1 [(41, 37)]))
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.break 0)
                        (Flapjack.WordLangProgHOL.move 1 [(41, 25)]))))
                  (Flapjack.WordLangProgHOL.tick))
                (Flapjack.WordLangProgHOL.move 1 [(21, 41)]))
              (Flapjack.Spt.bn
                (Flapjack.Spt.ln)
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                  (Flapjack.Spt.ln))))))
        (Flapjack.WordLangProgHOL.tick))
      (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 53 0x0000000000000000#64)))
    (Flapjack.WordLangProgHOL.seq (Flapjack.WordLangProgHOL.move 0 [(2, 53)]) (Flapjack.WordLangProgHOL.return 17 [2])))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Common-subexpression elimination leaves the countdown literal unchanged. -/
theorem countdown_cse_literal (x : BitVec 64) : WordCse.wordCommonSubexpElim (countdownDeadWord x) = countdownDeadWord x := by
  unfold countdownDeadWord
  simp only [WordCse.wordCommonSubexpElim,WordCse.wordCse,WordCse.wordCseInst]
  with_unfolding_all rfl

/-- Countdown code after copy propagation. -/
def countdownCopiedWord (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(9, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 13 x))
            (Flapjack.WordLangProgHOL.tick))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.move 0 [(17, 9), (21, 13)])
            (Flapjack.WordLangProgHOL.loop
              (Flapjack.Spt.bn
                (Flapjack.Spt.ln)
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ()))
                    (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                  (Flapjack.Spt.ln)))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.move 0 [(25, 21)])
                    (Flapjack.WordLangProgHOL.ite
                      (Flapjack.Cmp.notEqual)
                      25
                      (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.seq
                              (Flapjack.WordLangProgHOL.move 0 [(29, 25)])
                              (Flapjack.WordLangProgHOL.inst
                                (Flapjack.WordLangInst.arith
                                  (Flapjack.WordLangArith.binop
                                    (Flapjack.BinOp.add)
                                    33
                                    29
                                    (Flapjack.WordRegImm.imm 0xffffffffffffffff#64)))))
                            (Flapjack.WordLangProgHOL.move 0 [(37, 33)]))
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.move 1 [(21, 37)])
                            (Flapjack.WordLangProgHOL.continue 0)))
                        (Flapjack.WordLangProgHOL.move 1 [(41, 21)]))
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.break 0)
                        (Flapjack.WordLangProgHOL.move 1 [(41, 25)]))))
                  (Flapjack.WordLangProgHOL.tick))
                (Flapjack.WordLangProgHOL.move 1 [(21, 41)]))
              (Flapjack.Spt.bn
                (Flapjack.Spt.ln)
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                  (Flapjack.Spt.ln))))))
        (Flapjack.WordLangProgHOL.tick))
      (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 53 0x0000000000000000#64)))
    (Flapjack.WordLangProgHOL.seq (Flapjack.WordLangProgHOL.move 0 [(2, 53)]) (Flapjack.WordLangProgHOL.return 17 [2])))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Copy propagation emits this literal for every countdown value. -/
theorem countdown_copy_literal (x : BitVec 64) : WordCopy.copyProp (countdownDeadWord x) = countdownCopiedWord x := by
  unfold countdownDeadWord countdownCopiedWord
  simp only [WordCopy.copyProp,WordCopy.copyPropProg,WordCopy.copyPropInst]
  with_unfolding_all rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- RISC-V does not require two-register rewriting of this program. -/
theorem countdown_twoReg_literal (x : BitVec 64) : WordInst.threeToTwoRegProg riscvConfig.twoRegArith (countdownCopiedWord x) = countdownCopiedWord x := by
  unfold countdownCopiedWord
  simp only [WordInst.threeToTwoRegProg]
  with_unfolding_all rfl

/-- Countdown code after unreachable-code removal. -/
def countdownReachableWord (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(9, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 13 x))
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.tick)
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.move 0 [(17, 9), (21, 13)])
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.loop
            (Flapjack.Spt.bn
              (Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ()))
                  (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                (Flapjack.Spt.ln)))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.move 0 [(25, 21)])
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.ite
                  (Flapjack.Cmp.notEqual)
                  25
                  (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.move 0 [(29, 25)])
                    (Flapjack.WordLangProgHOL.seq
                      (Flapjack.WordLangProgHOL.inst
                        (Flapjack.WordLangInst.arith
                          (Flapjack.WordLangArith.binop
                            (Flapjack.BinOp.add)
                            33
                            29
                            (Flapjack.WordRegImm.imm 0xffffffffffffffff#64))))
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.move 1 [(21, 33), (37, 33)])
                        (Flapjack.WordLangProgHOL.continue 0))))
                  (Flapjack.WordLangProgHOL.break 0))
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.tick)
                  (Flapjack.WordLangProgHOL.move 1 [(21, 41)]))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())))
                (Flapjack.Spt.ln))))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.tick)
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 53 0x0000000000000000#64))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.move 0 [(2, 53)])
                (Flapjack.WordLangProgHOL.return 17 [2]))))))))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Unreachable-code removal emits this literal for every count. -/
theorem countdown_unreach_literal (x : BitVec 64) : WordUnreach.removeUnreach (countdownCopiedWord x) = countdownReachableWord x := by
  unfold countdownCopiedWord countdownReachableWord
  simp only [WordUnreach.removeUnreach,WordUnreach.seqAssocRight,WordUnreach.simpSeq]
  with_unfolding_all rfl

private def firstDeadRet : WordLangProgHOL (BitVec 64) := match countdownSsaWord 5 with
  | .seq _ (.seq _ t) => t | _ => .skip
private def firstDeadZero : WordLangProgHOL (BitVec 64) := match countdownSsaWord 5 with
  | .seq _ (.seq (.seq _ t) _) => t | _ => .skip
private def firstDeadLoopIn : WordLangProgHOL (BitVec 64) := match countdownSsaWord 5 with
  | .seq _ (.seq (.seq (.seq (.seq _ t) _) _) _) => t | _ => .skip
private def firstDeadLoopOut : WordLangProgHOL (BitVec 64) := match countdownDeadWord 5 with
  | .seq _ (.seq (.seq (.seq (.seq _ t) _) _) _) => t | _ => .skip
private def firstDeadLret : NumSet := .bn .ln (.bn (.bn (.bn .ln (.bn (.ls ()) .ln)) (.bn .ln (.ls ()))) .ln)
private def firstDeadLzero : NumSet := .bn .ln (.bn (.bn .ln (.bn .ln (.ls ()))) .ln)
private def firstDeadLloop : NumSet := .bn .ln (.bn (.bn (.ls ()) (.ls ())) .ln)
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem firstDeadRunRet : WordAlloc.removeDead firstDeadRet .ln [] [] = (firstDeadRet,firstDeadLret,[]) := by with_unfolding_all rfl
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem firstDeadRunZero : WordAlloc.removeDead firstDeadZero firstDeadLret [] [] = (firstDeadZero,firstDeadLzero,[]) := by with_unfolding_all rfl
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem firstDeadRunLoop : WordAlloc.removeDead firstDeadLoopIn firstDeadLzero [] [] = (firstDeadLoopOut,firstDeadLloop,[]) := by with_unfolding_all rfl

private theorem firstDeadPrefix (x : BitVec 64) (l a b c d : WordLangProgHOL (BitVec 64))
 (hr : WordAlloc.removeDead (.seq c d) .ln [] [] = (.seq c d,firstDeadLret,[]))
 (hz : WordAlloc.removeDead (.inst (.const 53 (0 : BitVec 64))) firstDeadLret [] [] = (.inst (.const 53 (0 : BitVec 64)),firstDeadLzero,[]))
 (hl : WordAlloc.removeDead l firstDeadLzero [] [] = (.seq a b,firstDeadLloop,[])) :
 WordAlloc.removeDeadProg
   (.seq (.move 1 [(9,0)]) (.seq (.seq (.seq (.seq (.seq (.inst (.const 13 x)) .tick) l) .tick) (.inst (.const 53 (0 : BitVec 64)))) (.seq c d))) =
   .seq (.move 1 [(9,0)]) (.seq (.seq (.seq (.seq (.seq (.inst (.const 13 x)) .tick) (.seq a b)) .tick) (.inst (.const 53 (0 : BitVec 64)))) (.seq c d)) := by
 simp only [WordAlloc.removeDeadProg,WordAlloc.removeDead,hr,hz,hl,WordAlloc.removeDeadInst,WordAlloc.removeDeadInstCore,WordAlloc.getLiveInst,WordAlloc.getLiveInstCore,WordAlloc.getLive]
 with_unfolding_all rfl

private def firstDeadOutA : WordLangProgHOL (BitVec 64) := match firstDeadLoopOut with | .seq a _ => a | _ => .skip
private def firstDeadOutB : WordLangProgHOL (BitVec 64) := match firstDeadLoopOut with | .seq _ b => b | _ => .skip
private theorem firstDeadLoopSplit : firstDeadLoopOut = .seq firstDeadOutA firstDeadOutB := by with_unfolding_all rfl
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The first dead-code pass emits the literal for every count. -/
theorem countdown_firstDead_literal (x : BitVec 64) : WordAlloc.removeDeadProg (countdownSsaWord x) = countdownDeadWord x := by
  have hin : countdownSsaWord x = .seq (.move 1 [(9,0)])
    (.seq (.seq (.seq (.seq (.seq (.inst (.const 13 x)) .tick) firstDeadLoopIn) .tick) (.inst (.const 53 0)))
      (.seq (.move 0 [(2,53)]) (.return 17 [2]))) := by
    unfold countdownSsaWord firstDeadLoopIn
    rfl
  have hout : countdownDeadWord x = .seq (.move 1 [(9,0)])
    (.seq (.seq (.seq (.seq (.seq (.inst (.const 13 x)) .tick) (.seq firstDeadOutA firstDeadOutB)) .tick) (.inst (.const 53 0)))
      (.seq (.move 0 [(2,53)]) (.return 17 [2]))) := by
    unfold countdownDeadWord firstDeadOutA firstDeadOutB firstDeadLoopOut
    rfl
  have hl : WordAlloc.removeDead firstDeadLoopIn firstDeadLzero [] [] = (.seq firstDeadOutA firstDeadOutB,firstDeadLloop,[]) := by
    rw [← firstDeadLoopSplit]
    exact firstDeadRunLoop
  have hr : WordAlloc.removeDead (.seq (.move 0 [(2,53)]) (.return 17 [2]) : WordLangProgHOL (BitVec 64)) .ln [] [] =
      (.seq (.move 0 [(2,53)]) (.return 17 [2]),firstDeadLret,[]) := by exact firstDeadRunRet
  have hz : WordAlloc.removeDead (.inst (.const 53 (0 : BitVec 64))) firstDeadLret [] [] =
      (.inst (.const 53 (0 : BitVec 64)),firstDeadLzero,[]) := by exact firstDeadRunZero
  rw [hin,hout]
  exact firstDeadPrefix x firstDeadLoopIn firstDeadOutA firstDeadOutB _ _ hr hz hl

end SteppedFlapjack.Concrete
