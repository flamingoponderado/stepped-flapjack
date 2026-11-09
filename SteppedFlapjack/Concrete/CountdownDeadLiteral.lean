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

end SteppedFlapjack.Concrete
