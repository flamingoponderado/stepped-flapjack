import SteppedFlapjack.Concrete.CountdownStackSpan
open Flapjack.Compiler.Backend.StackLang
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackAllocSteps

namespace SteppedFlapjack.Concrete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem constPrefix (x y : BitVec 64) (tail : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) :
 stackControlWeight (compNative riscvConfig false (.seq (.inst (.const 2 x)) tail) bs (countdownZeroLimit,0,0)).1 =
 stackControlWeight (compNative riscvConfig false (.seq (.inst (.const 2 y)) tail) bs (countdownZeroLimit,0,0)).1 := by
 simp only [compNative.eq_11,compNative.eq_3]
 simp [stackControlWeight,wInstNative,wRegWrite1Native,Flapjack.Compiler.Encoders.Asm.HolInst.ofWordLangInst, countdownZeroLimit,RowColoring.limit]
 split <;> simp_all [stackControlWeight]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem twoConstPrefix (x y : BitVec 64) (tail : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) :
 stackControlWeight (compNative riscvConfig false (.seq (.move 1 [(0,0)]) (.seq (.inst (.const 2 x)) tail)) bs (countdownZeroLimit,0,0)).1 =
 stackControlWeight (compNative riscvConfig false (.seq (.move 1 [(0,0)]) (.seq (.inst (.const 2 y)) tail)) bs (countdownZeroLimit,0,0)).1 := by
 conv_lhs => rw [compNative.eq_11,compNative.eq_2]
 conv_rhs => rw [compNative.eq_11,compNative.eq_2]
 simp only [stackControlWeight]
 exact congrArg (fun t => 1 + stackControlWeight (wMoveNative [(0,0)] (countdownZeroLimit,0,0)) + t) (constPrefix x y tail bs)

noncomputable def countdownCalleeSuffix : WordLangProgHOL (BitVec 64) :=
  match countdownOptimizedLoop 0 with
  | .seq _ (.seq _ tail) => tail
  | _ => .skip

theorem countdownOptimizedLoop_prefix (n : Nat) : countdownOptimizedLoop n =
 .seq (.move 1 [(0,0)]) (.seq (.inst (.const 2 (BitVec.ofNat 64 n))) countdownCalleeSuffix) := by rfl

private theorem loopWeight (n : Nat) (bs : AppList (BitVec 64) × Nat) :
 stackControlWeight (compNative riscvConfig false (countdownOptimizedLoop n) bs (countdownZeroLimit,0,0)).1 =
 stackControlWeight (compNative riscvConfig false (countdownOptimizedLoop 0) bs (countdownZeroLimit,0,0)).1 := by
 rw [countdownOptimizedLoop_prefix n,countdownOptimizedLoop_prefix 0]
 exact twoConstPrefix _ _ countdownCalleeSuffix bs

open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.WordToStackSteps
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem genericRow (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) :
 stackControlWeight (compileProgNative riscvConfig false p 1 countdownZeroLimit bs).1 =
 2 + stackControlWeight (compNative riscvConfig false p bs
  (countdownZeroLimit,nativeEntryFrameSize countdownZeroLimit p,nativeEntryFrame countdownZeroLimit p)).1 := by
 unfold compileProgNative nativeEntryFrameSize nativeEntryFrame nativeFrameSize nativeFrame
 generalize h : (max (maxVarHOL p / 2 + 1 - countdownZeroLimit) (1-countdownZeroLimit)) = frame
 cases e : compNative riscvConfig false p bs (countdownZeroLimit, (if frame = 0 then 0 else frame+1),frame) with
 | mk prog out =>
   simp only [stackControlWeight]
   rw [h,e]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem countdownCallee_frame_zero (n : Nat) : nativeEntryFrame countdownZeroLimit (countdownOptimizedLoop n) = 0 := by
  have h := countdownCallee_entryFrame_zero n
  unfold nativeEntryFrameSize nativeFrameSize at h
  change nativeFrame countdownZeroLimit 1 (countdownOptimizedLoop n) = 0
  dsimp only at h
  split at h <;> omega

private theorem rowInvariant (n : Nat) (bs : AppList (BitVec 64) × Nat) :
 stackControlWeight (compileProgNative riscvConfig false (countdownOptimizedLoop n) 1 countdownZeroLimit bs).1 =
 stackControlWeight (compileProgNative riscvConfig false (countdownOptimizedLoop 0) 1 countdownZeroLimit bs).1 := by
 rw [genericRow,genericRow,countdownCallee_entryFrame_zero,countdownCallee_entryFrame_zero,countdownCallee_frame_zero,countdownCallee_frame_zero,loopWeight]

open SteppedFlapjack.StackRemoveSteps.CompCorrect
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem tableCost (a b c : HolProg 64) (h : stackControlWeight b = stackControlWeight c) : loopCodeCost 0 (sptFromAList
 [(raiseStubLocation,raiseStubNative false countdownZeroLimit),(storeConstsStubLocation,storeConstsStubNative countdownZeroLimit),(64,a),(65,b)]) =
 loopCodeCost 0 (sptFromAList
 [(raiseStubLocation,raiseStubNative false countdownZeroLimit),(storeConstsStubLocation,storeConstsStubNative countdownZeroLimit),(64,a),(65,c)]) := by
 with_unfolding_all
  change maxListNat [linearLoopCost 0 b,linearLoopCost 0 (raiseStubNative false countdownZeroLimit : HolProg 64),linearLoopCost 0 a,linearLoopCost 0 (storeConstsStubNative countdownZeroLimit : HolProg 64)] =
    maxListNat [linearLoopCost 0 c,linearLoopCost 0 (raiseStubNative false countdownZeroLimit : HolProg 64),linearLoopCost 0 a,linearLoopCost 0 (storeConstsStubNative countdownZeroLimit : HolProg 64)]
 simp only [linearLoopCost,Nat.zero_add,Nat.mul_one,h]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem riscvNative_two_entry_code (p q : WordLangProgHOL (BitVec 64)) :
 (compileNative riscvConfig false [(64,1,p),(65,1,q)]).2.2.2 =
 [(raiseStubLocation,raiseStubNative false countdownZeroLimit),
  (storeConstsStubLocation,storeConstsStubNative countdownZeroLimit),
  (64,(compileProgNative riscvConfig false p 1 countdownZeroLimit (.list [4],1)).1),
  (65,(compileProgNative riscvConfig false q 1 countdownZeroLimit
    (compileProgNative riscvConfig false p 1 countdownZeroLimit (.list [4],1)).2.2).1)] := by
  unfold compileNative
  change (let (bodies,_,_) := compileWordToStackNative riscvConfig false countdownZeroLimit [(64,1,p),(65,1,q)] (.list [4],1)
   (raiseStubLocation,raiseStubNative false countdownZeroLimit) :: (storeConstsStubLocation,storeConstsStubNative countdownZeroLimit) :: bodies) = _
  unfold compileWordToStackNative
  cases h1 : compileProgNative riscvConfig false p 1 countdownZeroLimit (.list [4],1) with
  | mk first rest =>
    cases rest with
    | mk frame bitmap =>
      cases h2 : compileProgNative riscvConfig false q 1 countdownZeroLimit bitmap with
      | mk second rest =>
        cases rest with
        | mk frame2 bitmap2 => simp only [compileWordToStackNative,h2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem tableInvariant (n : Nat) : loopCodeCost 0 (sptFromAList (compileNative riscvConfig false
 (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2) =
 loopCodeCost 0 (sptFromAList (compileNative riscvConfig false
 (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms 0)).2).2.2.2) := by
 rw [countdown_optimized_literal,countdown_optimized_literal]
 have lit (k : Nat) : countdownOptimizedLiteral (BitVec.ofNat 64 k) = [(64,1,countdownOptimizedEntry),(65,1,countdownOptimizedLoop k)] := by rfl
 rw [lit n,lit 0,riscvNative_two_entry_code,riscvNative_two_entry_code]
 apply tableCost
 exact rowInvariant n _
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem zeroCost : loopCodeCost 0 (sptFromAList (compileNative riscvConfig false
 (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms 0)).2).2.2.2) = 34 := by
 rw [countdown_optimized_literal]
 with_unfolding_all rfl
open SteppedFlapjack.WordSimpSteps
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem entryCost (code : Spt (HolProg 64)) :
 callSequenceCost riscvConfig 0 code countdownOptimizedEntry (.list [4],1) (countdownZeroLimit,0,0) = 7 + loopCodeCost 0 code := by
  have h : stackControlWeight (wMoveNative [(0,0)] (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length),0,0) : HolProg 64) = 1 := by with_unfolding_all rfl
  simp [countdownOptimizedEntry,callSequenceCost.eq_def,loopWord,straightWord,linearLoopCost,loopOnlyCost,callDestNative,compNative,countdownZeroLimit,RowColoring.limit,h]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Closed linear native Stack visit bound for every countdown input. -/
theorem countdown_stackBound_closed (n limit : Nat) : nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n) limit = 3 + 41*(limit+1) := by
 have selected : nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n) = countdownOptimizedEntry := countdown_compilerSelectedEntry n
 have cursor : nativeTailEntryBitmap countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 = (.list [4],1) := by
   unfold nativeTailEntryBitmap
   rw [countdown_optimized_literal]
   rfl
 have size : nativeEntryFrameSize countdownZeroLimit countdownOptimizedEntry = 0 := by with_unfolding_all rfl
 have frame : nativeEntryFrame countdownZeroLimit countdownOptimizedEntry = 0 := by with_unfolding_all rfl
 unfold nativeTailEntryBound
 rw [selected,cursor]
 change 3 + callSequenceCost riscvConfig 0 _ countdownOptimizedEntry (.list [4],1)
   (countdownZeroLimit,nativeEntryFrameSize countdownZeroLimit countdownOptimizedEntry,nativeEntryFrame countdownZeroLimit countdownOptimizedEntry) * (limit+1) = _
 rw [size,frame,entryCost,tableInvariant n,zeroCost]

end SteppedFlapjack.Concrete
