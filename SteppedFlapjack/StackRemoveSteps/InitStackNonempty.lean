import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
namespace SteppedFlapjack.StackRemoveSteps

/-- The total initializer always supplies at least the sentinel stack word. -/
theorem makeInitAny_stack_nonempty {width : Nat} [NeZero width] {C F : Type}
    (ggc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    1 ≤ (InitMake.makeInitAny ggc maxHeap bitmaps dataSpace oracle jump bounds pointer code s).stack.length := by
  unfold InitMake.makeInitAny
  split
  · rename_i t ht
    unfold InitMake.makeInitOpt at ht
    split at ht
    · contradiction
    · split at ht
      · cases ht
        simp [InitReduce.initReduce, Flapjack.Compiler.Backend.StackRemove.length_readMem]
      · contradiction
  · simp

/-- The complete Stack initializer preserves the nonempty sentinel stack. -/
theorem fullMakeInit_stack_nonempty {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : Flapjack.Compiler.Backend.LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    1 ≤ (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1.stack.length := by
  unfold fullMakeInit StackAlloc.makeInit
  exact makeInitAny_stack_nonempty _ _ _ _ _ _ _ _ _ _

end SteppedFlapjack.StackRemoveSteps
