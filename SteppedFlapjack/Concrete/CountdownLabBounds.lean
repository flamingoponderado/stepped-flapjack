import SteppedFlapjack.StackToLabSteps.ConstantPrefix
import SteppedFlapjack.Concrete.CountdownInitE
import SteppedFlapjack.Concrete.CountdownStackBounds
import SteppedFlapjack.Concrete.FixtureLabNumeric
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

namespace SteppedFlapjack.Concrete

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem sameInfo (x y : BitVec 64) (a b c tail : HolProg 64) :
 StackRawCall.collectInfo (SteppedFlapjack.Phase6.prefixCode x a b c tail) .ln =
 StackRawCall.collectInfo (SteppedFlapjack.Phase6.prefixCode y a b c tail) .ln := by
 simp [SteppedFlapjack.Phase6.prefixCode,SteppedFlapjack.Phase6.P,StackRawCall.collectInfo,StackRawCall.seqStackAlloc]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem rawPrefix (x : BitVec 64) (tail : HolProg 64) (info : Spt Nat) :
 StackRawCall.compTop info (.seq (.stackAlloc 0) (.seq .skip (.seq (.inst (.const 1 x)) tail))) =
 .seq (.stackAlloc 0) (.seq .skip (.seq (.inst (.const 1 x)) (StackRawCall.comp info tail))) := by
 simp [StackRawCall.compTop,StackRawCall.comp,StackRawCall.compSeq,StackRawCall.destCase]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem allocPrefixCost (B : Nat) (bounds : BitVec 64 × BitVec 64) (x y : BitVec 64) (tail : HolProg 64) :
 leafCost B bounds (StackAlloc.progComp (65,.seq (.stackAlloc 0) (.seq .skip (.seq (.inst (.const 1 x)) tail)))).2 =
 leafCost B bounds (StackAlloc.progComp (65,.seq (.stackAlloc 0) (.seq .skip (.seq (.inst (.const 1 y)) tail)))).2 := by
 simp [StackAlloc.progComp,StackAlloc.nextLabHOL,StackAlloc.nextLab,StackAlloc.comp,leafCost,rawLeafCost]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem code1Prefix (x : BitVec 64) (a b c tail : HolProg 64) :
 code1 countdownRiscVBackend.dataConf (SteppedFlapjack.Phase6.prefixCode x a b c tail) =
 let info := StackRawCall.collectInfo (SteppedFlapjack.Phase6.prefixCode x a b c tail) .ln
 [(gcStubLocation, .seq (StackAlloc.wordGcCode countdownRiscVBackend.dataConf) (.ret 0)),
  StackAlloc.progComp (5,StackRawCall.compTop info a),
  StackAlloc.progComp (6,StackRawCall.compTop info b),
  StackAlloc.progComp (64,StackRawCall.compTop info c),
  StackAlloc.progComp (65,.seq (.stackAlloc 0) (.seq .skip (.seq (.inst (.const 1 x)) (StackRawCall.comp info tail))))] := by
 unfold code1 StackAlloc.compile StackRawCall.compile SteppedFlapjack.Phase6.prefixCode SteppedFlapjack.Phase6.P
 simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,StackAlloc.stubs]
 rw [rawPrefix]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem codeTreeCost (B : Nat) (bounds : BitVec 64 × BitVec 64) (g a b c p q : HolProg 64)
 (h : leafCost B bounds p = leafCost B bounds q) :
 maxListNat ((sptToAList (sptFromAList [(gcStubLocation,g),(5,a),(6,b),(64,c),(65,p)])).map fun e => leafCost B bounds e.2) =
 maxListNat ((sptToAList (sptFromAList [(gcStubLocation,g),(5,a),(6,b),(64,c),(65,q)])).map fun e => leafCost B bounds e.2) := by
 with_unfolding_all
  change maxListNat [leafCost B bounds p,leafCost B bounds a,leafCost B bounds c,leafCost B bounds g,leafCost B bounds b] =
   maxListNat [leafCost B bounds q,leafCost B bounds a,leafCost B bounds c,leafCost B bounds g,leafCost B bounds b]
 rw [h]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem prefixFactor (x y : BitVec 64) (a b c tail : HolProg 64) (cfg : LabToTarget.Config) :
 costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none)
   (sptFromAList (code1 countdownRiscVBackend.dataConf (SteppedFlapjack.Phase6.prefixCode x a b c tail))) [4] (coracle1 (fixtureStackOracle cfg)) =
 costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none)
   (sptFromAList (code1 countdownRiscVBackend.dataConf (SteppedFlapjack.Phase6.prefixCode y a b c tail))) [4] (coracle1 (fixtureStackOracle cfg)) := by
 rw [code1Prefix x,code1Prefix y,sameInfo x y a b c tail]
 simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
 congr 3
 apply codeTreeCost
 exact allocPrefixCost _ _ x y _


set_option maxHeartbeats 400000 in
private theorem nativePrefix (x : BitVec 64) (tail : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) :
 compNative riscvConfig false (.seq (.move 1 [(0,0)]) (.seq (.inst (.const 2 x)) tail)) bs (countdownZeroLimit,0,0) =
 let r := compNative riscvConfig false tail bs (countdownZeroLimit,0,0)
 (.seq (wMoveNative [(0,0)] (countdownZeroLimit,0,0)) (.seq (.inst (.const 1 x)) r.1), r.2) := by
 simp only [compNative.eq_11,compNative.eq_2,compNative.eq_3]
 simp [wInstNative,wRegWrite1Native,HolInst.ofWordLangInst,countdownZeroLimit,RowColoring.limit]
 with_unfolding_all decide
open SteppedFlapjack.WordToStackSteps
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem zeroFrameCompile (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
 (hs : nativeEntryFrameSize countdownZeroLimit p = 0) (hf : nativeEntryFrame countdownZeroLimit p = 0) :
 compileProgNative riscvConfig false p 1 countdownZeroLimit bs =
 (.seq (.stackAlloc 0) (compNative riscvConfig false p bs (countdownZeroLimit,0,0)).1,0,
   (compNative riscvConfig false p bs (countdownZeroLimit,0,0)).2) := by
 change (let arg := 1-countdownZeroLimit; let frame := nativeEntryFrame countdownZeroLimit p;
   let size := nativeEntryFrameSize countdownZeroLimit p;
   let z := compNative riscvConfig false p bs (countdownZeroLimit,size,frame);
   (StackLang.Prog.seq (.stackAlloc (size-arg)) z.1,size,z.2)) = _
 rw [hs,hf]
 simp only [Nat.zero_sub]

noncomputable def countdownFirstNative : HolProg 64 :=
 (compileProgNative riscvConfig false countdownOptimizedEntry 1 countdownZeroLimit (.list [4],1)).1
private noncomputable def firstCursor : AppList (BitVec 64) × Nat :=
 (compileProgNative riscvConfig false countdownOptimizedEntry 1 countdownZeroLimit (.list [4],1)).2.2
noncomputable def countdownFixedTail : HolProg 64 :=
 (compNative riscvConfig false countdownCalleeSuffix firstCursor (countdownZeroLimit,0,0)).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem countdown_nativeShape (n : Nat) : countdownNativeStackCode n =
 SteppedFlapjack.Phase6.prefixCode (BitVec.ofNat 64 n) (raiseStubNative false countdownZeroLimit) (storeConstsStubNative countdownZeroLimit) countdownFirstNative countdownFixedTail := by
 have lit : countdownOptimizedLiteral (BitVec.ofNat 64 n) = [(64,1,countdownOptimizedEntry),(65,1,countdownOptimizedLoop n)] := by rfl
 unfold countdownNativeStackCode
 rw [countdown_optimized_literal,lit,riscvNative_two_entry_code]
 have frame := countdownCallee_frame_zero n
 have size := countdownCallee_entryFrame_zero n
 change [(raiseStubLocation,raiseStubNative false countdownZeroLimit),
   (storeConstsStubLocation,storeConstsStubNative countdownZeroLimit),(64,countdownFirstNative),
   (65,(compileProgNative riscvConfig false (countdownOptimizedLoop n) 1 countdownZeroLimit firstCursor).1)] = _
 rw [zeroFrameCompile _ firstCursor size frame,countdownOptimizedLoop_prefix,nativePrefix]
 have move : (wMoveNative [(0,0)] (countdownZeroLimit,0,0) : HolProg 64) = .skip := by with_unfolding_all rfl
 rw [move]
 rfl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
private theorem actualFactor (n : Nat) (cfg : LabToTarget.Config) :
 costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none)
   (sptFromAList (code1 countdownRiscVBackend.dataConf (countdownNativeStackCode n))) [4] (coracle1 (fixtureStackOracle cfg)) =
 costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none)
   (sptFromAList (code1 countdownRiscVBackend.dataConf (countdownNativeStackCode 0))) [4] (coracle1 (fixtureStackOracle cfg)) := by
 rw [countdown_nativeShape n,countdown_nativeShape 0]
 exact prefixFactor _ _ _ _ _ _ cfg

open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackToLabSteps
open Flapjack.Compiler.Backend.StackRemove

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem countdownZeroLabFactor (cfg : LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (countdownNativeStackCode 0))) [4]
      (coracle1 (fixtureStackOracle cfg)) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  unfold countdownNativeStackCode
  rw [countdown_optimized_literal]
  decide +kernel

/-- The initialized countdown Lab clock is a numeric affine function of the
source count. -/
theorem countdownLabTick_closed (n : Nat) (cfg : LabToTarget.Config) :
    fixtureLabTickLimit (countdownNativeStackCode n) cfg (9543650688*n+29426459323) =
      1060776773971200*n + 3270750953752551 := by
  have factor := (actualFactor n cfg).trans (countdownZeroLabFactor cfg)
  rw [fixtureLabTick_numeric _ _ _ factor]
  omega

end SteppedFlapjack.Concrete
