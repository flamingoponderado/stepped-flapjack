import SteppedFlapjack.Concrete.CountdownDeadLiteral
import SteppedFlapjack.PanToCrepSteps.CountdownColoring
open Flapjack Flapjack.RegAlloc Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps
namespace SteppedFlapjack.Concrete

/-- Countdown code immediately before register allocation. -/
def countdownAllocationInput (x : BitVec 64) : WordLangProgHOL (BitVec 64) :=
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
                        (Flapjack.WordLangProgHOL.move 1 [(21, 33)])
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

private theorem clash_constant (x y : BitVec 64) (pre tail : WordLangProgHOL (BitVec 64)) (lt : List (NumSet × NumSet)) :
 WordAlloc.getClashTree (.seq pre (.seq (.inst (.const 13 x)) tail)) lt =
 WordAlloc.getClashTree (.seq pre (.seq (.inst (.const 13 y)) tail)) lt := by
 simp only [WordAlloc.getClashTree,WordAlloc.getDeltaInst]
 rfl

private theorem stack_constant (x y : BitVec 64) (pre tail : WordLangProgHOL (BitVec 64)) :
 WordAlloc.getStackOnly (.seq pre (.seq (.inst (.const 13 x)) tail)) =
 WordAlloc.getStackOnly (.seq pre (.seq (.inst (.const 13 y)) tail)) := by
 simp only [WordAlloc.getStackOnly,WordAlloc.getStackOnlyAux,WordAlloc.getClashTree,WordAlloc.getDeltaInst]
 rfl

private theorem forced_constant (x y : BitVec 64) (pre tail : WordLangProgHOL (BitVec 64)) :
 WordAlloc.getForced riscvConfig (.seq pre (.seq (.inst (.const 13 x)) tail)) [] =
 WordAlloc.getForced riscvConfig (.seq pre (.seq (.inst (.const 13 y)) tail)) [] := by
 simp only [WordAlloc.getForced]

private theorem heuristic_constant (x y : BitVec 64) (pre tail : WordLangProgHOL (BitVec 64)) :
 WordAlloc.getHeuristics 3 65 (.seq pre (.seq (.inst (.const 13 x)) tail)) =
 WordAlloc.getHeuristics 3 65 (.seq pre (.seq (.inst (.const 13 y)) tail)) := by
 simp only [WordAlloc.getHeuristics,WordAlloc.getHeu,WordAlloc.getPrefs]
 generalize WordAlloc.getHeu 65 pre (.ln,.ln) = st
 rcases st with ⟨tracked,calls⟩
 simp only [WordAlloc.getHeu,WordAlloc.getHeuInst]

/-- The complete register-allocation input is independent of the count. -/
theorem countdown_allocation_inputs (x y : BitVec 64) :
    WordAlloc.getClashTree (countdownAllocationInput x) [] = WordAlloc.getClashTree (countdownAllocationInput y) [] ∧
    WordAlloc.getStackOnly (countdownAllocationInput x) = WordAlloc.getStackOnly (countdownAllocationInput y) ∧
    WordAlloc.getForced riscvConfig (countdownAllocationInput x) [] = WordAlloc.getForced riscvConfig (countdownAllocationInput y) [] ∧
    WordAlloc.getHeuristics 3 65 (countdownAllocationInput x) = WordAlloc.getHeuristics 3 65 (countdownAllocationInput y) := by
  unfold countdownAllocationInput
  exact ⟨clash_constant x y _ _ [], stack_constant x y _ _, forced_constant x y _ _, heuristic_constant x y _ _⟩

private theorem countdownAllocationInput_zero : countdownAllocationInput 0 = countdownZeroAllocInput := by with_unfolding_all rfl
/-- The original checked graph coloring applies to every countdown value. -/
theorem countdown_allocation_color (x : BitVec 64) : regAllocExecutable .IRC
    (WordAlloc.getHeuristics 3 65 (countdownAllocationInput x)).2 countdownZeroLimit
    (WordAlloc.getHeuristics 3 65 (countdownAllocationInput x)).1
    (WordAlloc.getClashTree (countdownAllocationInput x) [])
    (WordAlloc.getForced riscvConfig (countdownAllocationInput x) [])
    (WordAlloc.getStackOnly (countdownAllocationInput x)) = .success countdownZeroColor := by
  have same := countdown_allocation_inputs x 0
  rw [same.1,same.2.1,same.2.2.1,same.2.2.2,countdownAllocationInput_zero]
  simpa only [countdownZeroMoves,countdownZeroClashTree,countdownZeroForced,RowColoring.forced,RowColoring.input,countdownZeroAllocInput,countdownZeroColor,
    show countdownZeroLoopRow.1 = 65 by rfl] using countdownZero_graphAllocation_exact

/-- The complete register-allocated countdown Word table. -/
def countdownOptimizedLiteral (x : BitVec 64) : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
[(64,
  1,
  Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
    (Flapjack.WordLangProgHOL.call none (some 65) [0] none)),
 (65,
  1,
  Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 x))
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.tick)
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.move 0 [(0, 0), (2, 2)])
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.loop
              (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.ln))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.ite
                    (Flapjack.Cmp.notEqual)
                    2
                    (Flapjack.WordRegImm.imm 0x0000000000000000#64)
                    (Flapjack.WordLangProgHOL.seq
                      (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.inst
                          (Flapjack.WordLangInst.arith
                            (Flapjack.WordLangArith.binop
                              (Flapjack.BinOp.add)
                              2
                              2
                              (Flapjack.WordRegImm.imm 0xffffffffffffffff#64))))
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.move 1 [(2, 2)])
                          (Flapjack.WordLangProgHOL.continue 0))))
                    (Flapjack.WordLangProgHOL.break 0))
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.tick)
                    (Flapjack.WordLangProgHOL.move 1 [(2, 2)]))))
              (Flapjack.Spt.ls ()))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.tick)
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 0x0000000000000000#64))
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
                  (Flapjack.WordLangProgHOL.return 0 [2])))))))))]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Applying the checked coloring emits the literal callee. -/
theorem countdown_apply_color_literal (x : BitVec 64) :
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour countdownZeroColor) (countdownAllocationInput x)) =
    ((countdownOptimizedLiteral x).get ⟨1,by simp [countdownOptimizedLiteral]⟩).2.2 := by
  unfold countdownAllocationInput countdownOptimizedLiteral
  simp only [WordAlloc.applyColour,WordRemove.removeMustTerminate]
  with_unfolding_all rfl

private theorem allocateWith_coloring (p : WordLangProgHOL (BitVec 64)) (color : Spt Nat)
  (h : regAllocExecutable .IRC (WordAlloc.getHeuristics 3 65 p).2 countdownZeroLimit
    (WordAlloc.getHeuristics 3 65 p).1 (WordAlloc.getClashTree p [])
    (WordAlloc.getForced riscvConfig p []) (WordAlloc.getStackOnly p) = .success color) :
  wordAllocWith regAllocExecutable 65 riscvConfig 3 countdownZeroLimit p none =
  WordAlloc.applyColour (WordAlloc.totalColour color) p := by
  simp only [wordAllocWith,WordAlloc.oracleColourOk,selectRegAllocWith,show ¬ 4 ≤ 3 by decide,if_false,show ¬ 3 ≤ 1 by decide]
  rw [h]
/-- The actual allocator applies the checked coloring for every count. -/
theorem countdown_wordAlloc_literal (x : BitVec 64) : wordAllocWith regAllocExecutable 65 riscvConfig 3 countdownZeroLimit (countdownAllocationInput x) none =
  WordAlloc.applyColour (WordAlloc.totalColour countdownZeroColor) (countdownAllocationInput x) :=
  allocateWith_coloring _ _ (countdown_allocation_color x)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The optimized generated entry contains a direct tail call. -/
theorem countdown_entry_optimized : fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
  ((64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),none) =
  (64,1,.seq (.move 1 [(0,0)]) (.call none (some 65) [0] none)) := by
  with_unfolding_all rfl

private def secondDeadLive : NumSet := .bn .ln (.bn (.bn (.ls ()) (.ls ())) .ln)
private theorem secondDeadPrefix (x : BitVec 64) (tail a b : WordLangProgHOL (BitVec 64))
 (h : WordAlloc.removeDead tail .ln [] [] = (.seq a b,secondDeadLive,[])) :
 WordAlloc.removeDeadProg (.seq (.move 1 [(9,0)]) (.seq (.inst (.const 13 x)) tail)) =
   .seq (.move 1 [(9,0)]) (.seq (.inst (.const 13 x)) (.seq a b)) := by
  simp only [WordAlloc.removeDeadProg,WordAlloc.removeDead,h,WordAlloc.removeDeadInst,WordAlloc.removeDeadInstCore,WordAlloc.getLiveInst,WordAlloc.getLiveInstCore]
  with_unfolding_all rfl

private def secondDeadTail : WordLangProgHOL (BitVec 64) := match countdownReachableWord 5 with
  | .seq _ (.seq _ t) => t
  | _ => .skip
private def secondDeadRest : WordLangProgHOL (BitVec 64) := match countdownAllocationInput 5 with
  | .seq _ (.seq _ (.seq _ t)) => t
  | _ => .skip
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem secondDeadTailRun : WordAlloc.removeDead secondDeadTail .ln [] [] = (.seq .tick secondDeadRest,secondDeadLive,[]) := by
  with_unfolding_all rfl

/-- The second dead-code pass emits the allocator input for every count. -/
theorem countdown_secondDead_literal (x : BitVec 64) : WordAlloc.removeDeadProg (countdownReachableWord x) = countdownAllocationInput x := by
  have hin : countdownReachableWord x = .seq (.move 1 [(9,0)]) (.seq (.inst (.const 13 x)) secondDeadTail) := by
    unfold countdownReachableWord secondDeadTail
    rfl
  have hout : countdownAllocationInput x = .seq (.move 1 [(9,0)]) (.seq (.inst (.const 13 x)) (.seq .tick secondDeadRest)) := by
    unfold countdownAllocationInput secondDeadRest
    rfl
  rw [hin,hout]
  exact secondDeadPrefix x secondDeadTail .tick secondDeadRest secondDeadTailRun

end SteppedFlapjack.Concrete
