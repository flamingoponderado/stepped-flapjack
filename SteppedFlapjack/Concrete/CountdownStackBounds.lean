import SteppedFlapjack.Concrete.CountdownStackSpan
open Flapjack.Compiler.Backend.StackLang
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackAllocSteps

namespace SteppedFlapjack.Concrete

noncomputable def countdownCalleeSuffix : WordLangProgHOL (BitVec 64) :=
  match countdownOptimizedLoop 0 with
  | .seq _ (.seq _ tail) => tail
  | _ => .skip

theorem countdownOptimizedLoop_prefix (n : Nat) : countdownOptimizedLoop n =
 .seq (.move 1 [(0,0)]) (.seq (.inst (.const 2 (BitVec.ofNat 64 n))) countdownCalleeSuffix) := by rfl

open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.WordToStackSteps
set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem countdownCallee_frame_zero (n : Nat) : nativeEntryFrame countdownZeroLimit (countdownOptimizedLoop n) = 0 := by
  have h := countdownCallee_entryFrame_zero n
  unfold nativeEntryFrameSize nativeFrameSize at h
  change nativeFrame countdownZeroLimit 1 (countdownOptimizedLoop n) = 0
  dsimp only at h
  split at h <;> omega

open SteppedFlapjack.StackRemoveSteps.CompCorrect
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

open SteppedFlapjack.WordSimpSteps
end SteppedFlapjack.Concrete
