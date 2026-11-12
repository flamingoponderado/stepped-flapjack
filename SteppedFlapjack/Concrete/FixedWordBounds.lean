import SteppedFlapjack.Concrete.ComparisonWordSpan
import SteppedFlapjack.Concrete.BranchingWordSpan
import SteppedFlapjack.Concrete.CountdownOptimized
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import SteppedFlapjack.PanToCrepSteps.CountdownWordLiteral
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang
open SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps
namespace SteppedFlapjack.Concrete

private def comparisonBoundWord : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0x0000000000000000#64))
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0x0000000000000001#64))
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.ite
          (Flapjack.Cmp.lower)
          8
          (Flapjack.WordRegImm.reg 2)
          (Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0x0000000000000001#64))
          (Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0x0000000000000000#64)))
        (Flapjack.WordLangProgHOL.tick))
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8))
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.ite
              (Flapjack.Cmp.notEqual)
              6
              (Flapjack.WordRegImm.imm 0x0000000000000000#64)
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0x0000000000000007#64))
                (Flapjack.WordLangProgHOL.seq (Flapjack.WordLangProgHOL.return 0 [4]) (Flapjack.WordLangProgHOL.skip)))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0x0000000000000009#64))
                (Flapjack.WordLangProgHOL.seq (Flapjack.WordLangProgHOL.return 0 [4]) (Flapjack.WordLangProgHOL.skip))))
            (Flapjack.WordLangProgHOL.tick))
          (Flapjack.WordLangProgHOL.skip)))))

private def comparisonBoundAlloc : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(13, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.tick)
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 33 0x0000000000000007#64))
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.move 0 [(2, 33)])
        (Flapjack.WordLangProgHOL.return 13 [2]))))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem preEq : countdownPreAllocation 1 comparisonBoundWord = comparisonBoundAlloc := by with_unfolding_all rfl

private theorem allocWeight : wordControlWeight (WordRemove.removeMustTerminate (wordAllocWith Flapjack.RegAlloc.regAllocExecutable 65 riscvConfig 3
 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) comparisonBoundAlloc none)) = 9 := by
  unfold wordAllocWith
  simp only [WordAlloc.oracleColourOk]
  split <;> simp [comparisonBoundAlloc,WordAlloc.applyColour,WordRemove.removeMustTerminate,wordControlWeight]

private theorem compWeight : wordControlWeight (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith
 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) 3 riscvConfig ((65,1,comparisonBoundWord),none)).2.2 = 9 := by
  change wordControlWeight (WordRemove.removeMustTerminate (wordAllocWith Flapjack.RegAlloc.regAllocExecutable 65 riscvConfig 3
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (countdownPreAllocation 1 comparisonBoundWord) none)) = 9
  rw [preEq]
  exact allocWeight

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem frontend : loopToWordCompFuncHOL 65 [] (twoCallee riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody) = comparisonBoundWord := by
  unfold comparisonBoundWord
  with_unfolding_all rfl

private theorem entryWeight : wordControlWeight (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith
 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) 3 riscvConfig
 ((64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),none)).2.2 = 3 := by
  have h := countdown_entry_optimized
  have he : loopToWordCompFuncHOL 64 [] branchingLoopEntry = .seq .skip (.seq (.call none (some 65) [0] none) .skip) := by with_unfolding_all rfl
  rw [he]
  change wordControlWeight (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig _).2.2 = 3
  rw [h]
  rfl


private theorem twoBound (arch : AsmArchitecture) (name callee : MlString) (body : CrepProgHOL 64) (fresh : name ≠ callee) (limit : Nat) :
 twoProgramWordBound arch name callee body limit phase3WordConfig riscvConfig =
  1 + wordControlWeight (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) 3 riscvConfig
      ((64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),none)).2.2 *
  (wordControlWeight (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) 3 riscvConfig
      ((65,1,loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body)),none)).2.2 + 1) * (6*limit+2) := by
  unfold twoProgramWordBound
  rw [twoLoops_exact arch name callee body fresh]
  rfl

private def branchWord : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.skip)
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0x0000000000000002#64))
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.tick)
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.loop
            (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())) () (Flapjack.Spt.ln))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.ite
                    (Flapjack.Cmp.notEqual)
                    10
                    (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                    (Flapjack.WordLangProgHOL.seq
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4))
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0x0000000000000002#64))
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.seq
                              (Flapjack.WordLangProgHOL.ite
                                (Flapjack.Cmp.equal)
                                2
                                (Flapjack.WordRegImm.reg 8)
                                (Flapjack.WordLangProgHOL.assign
                                  2
                                  (Flapjack.WordLangExpHOL.const 0x0000000000000001#64))
                                (Flapjack.WordLangProgHOL.assign
                                  2
                                  (Flapjack.WordLangExpHOL.const 0x0000000000000000#64)))
                              (Flapjack.WordLangProgHOL.tick))
                            (Flapjack.WordLangProgHOL.seq
                              (Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2))
                              (Flapjack.WordLangProgHOL.seq
                                (Flapjack.WordLangProgHOL.seq
                                  (Flapjack.WordLangProgHOL.ite
                                    (Flapjack.Cmp.notEqual)
                                    6
                                    (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                                    (Flapjack.WordLangProgHOL.seq
                                      (Flapjack.WordLangProgHOL.seq
                                        (Flapjack.WordLangProgHOL.assign
                                          4
                                          (Flapjack.WordLangExpHOL.const 0x0000000000000001#64))
                                        (Flapjack.WordLangProgHOL.skip))
                                      (Flapjack.WordLangProgHOL.skip))
                                    (Flapjack.WordLangProgHOL.seq
                                      (Flapjack.WordLangProgHOL.seq
                                        (Flapjack.WordLangProgHOL.assign
                                          4
                                          (Flapjack.WordLangExpHOL.const 0x0000000000000000#64))
                                        (Flapjack.WordLangProgHOL.skip))
                                      (Flapjack.WordLangProgHOL.skip)))
                                  (Flapjack.WordLangProgHOL.tick))
                                (Flapjack.WordLangProgHOL.skip))))))
                      (Flapjack.WordLangProgHOL.continue 0))
                    (Flapjack.WordLangProgHOL.break 0))
                  (Flapjack.WordLangProgHOL.tick))
                (Flapjack.WordLangProgHOL.skip)))
            (Flapjack.Spt.ls ()))
          (Flapjack.WordLangProgHOL.tick)))
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0x0000000000000007#64))
        (Flapjack.WordLangProgHOL.seq (Flapjack.WordLangProgHOL.return 0 [10]) (Flapjack.WordLangProgHOL.skip)))))

private def branchAlloc : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(13, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 17 0x0000000000000002#64))
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.tick)
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.move 0 [(21, 13), (25, 17)])
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.loop
            (Flapjack.Spt.bn
              (Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ()))
                  (Flapjack.Spt.bn (Flapjack.Spt.ls ()) (Flapjack.Spt.ln)))
                (Flapjack.Spt.ln)))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.move 0 [(29, 25)])
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.ite
                  (Flapjack.Cmp.notEqual)
                  29
                  (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.move 0 [(33, 29)])
                    (Flapjack.WordLangProgHOL.seq
                      (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 37 0x0000000000000002#64))
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.ite
                          (Flapjack.Cmp.equal)
                          33
                          (Flapjack.WordRegImm.reg 37)
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.tick)
                            (Flapjack.WordLangProgHOL.seq
                              (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 49 0x0000000000000001#64))
                              (Flapjack.WordLangProgHOL.move 1 [(73, 49)])))
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.tick)
                            (Flapjack.WordLangProgHOL.seq
                              (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 61 0x0000000000000000#64))
                              (Flapjack.WordLangProgHOL.move 1 [(73, 61)]))))
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.tick)
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.move 1 [(25, 73)])
                            (Flapjack.WordLangProgHOL.continue 0))))))
                  (Flapjack.WordLangProgHOL.break 0))
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.tick)
                  (Flapjack.WordLangProgHOL.move 1 [(25, 77)]))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ln) (Flapjack.Spt.ls ())) (Flapjack.Spt.ln))
                (Flapjack.Spt.ln))))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.tick)
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 93 0x0000000000000007#64))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.move 0 [(2, 93)])
                (Flapjack.WordLangProgHOL.return 21 [2]))))))))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem branchFrontend : loopToWordCompFuncHOL 65 [] (twoCallee riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody) = branchWord := by
  unfold branchWord
  with_unfolding_all rfl
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem branchPreEq : countdownPreAllocation 1 branchWord = branchAlloc := by with_unfolding_all rfl
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem branchAllocWeight : wordControlWeight (WordRemove.removeMustTerminate (wordAllocWith Flapjack.RegAlloc.regAllocExecutable 65 riscvConfig 3
 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) branchAlloc none)) = 46 := by
  unfold wordAllocWith
  simp only [WordAlloc.oracleColourOk]
  split <;> simp [branchAlloc,WordAlloc.applyColour,WordRemove.removeMustTerminate,wordControlWeight]
private theorem branchWeight : wordControlWeight (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith
 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) 3 riscvConfig ((65,1,branchWord),none)).2.2 = 46 := by
  change wordControlWeight (WordRemove.removeMustTerminate (wordAllocWith Flapjack.RegAlloc.regAllocExecutable 65 riscvConfig 3
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (countdownPreAllocation 1 branchWord) none)) = 46
  rw [branchPreEq]
  exact branchAllocWeight

/-- Numeric Word visit bound for the branching-loop witness. -/
theorem branch_bound_closed : branchWordBound = 6344939371 := by
  have h := twoBound riscvConfig.isa (ofString "main") (entryName (Flapjack.Pancake.PanLang.progToHOL branchingLoop)) branchingLoopCrepBody
    (Ne.symm (entryName_fresh (Flapjack.Pancake.PanLang.progToHOL branchingLoop))) branchLoopVisits
  simp only [branchFrontend,entryWeight,branchWeight] at h
  simpa [branchWordBound,branchLoopVisits,branchLoopBudget] using h

end SteppedFlapjack.Concrete
