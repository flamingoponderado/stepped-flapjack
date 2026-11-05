import SteppedFlapjack.StackAllocSteps.GcMoveClock

/-! Step bounds for simple collector bitmap traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A clock-based bound for the collector bitmap loop. -/
theorem gcMoveBitmapClockBound (k : Nat) (conf : Config) :
    ClockBound (C := C) (F := F) k (wordGcMoveBitmapCode conf : HolProg width)
      ((120 + 12 * (k + 1)) * (k + 1)) := by
  have ht := clockBoundSeq k _ _ _ _
    (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 7 1 : HolProg width) rfl)
    (clockBoundLeaf (C := C) (F := F) k (addBytesInWordInst 8 : HolProg width) rfl)
  have hf := clockBoundSeq k _ _ _ _
    (clockBoundLeaf (C := C) (F := F) k (.stackLoadAny 5 8 : HolProg width) rfl)
    (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 7 1 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _ (gcMoveClockBound (C := C) (F := F) (width := width) k conf)
        (clockBoundSeq k _ _ _ _
          (clockBoundLeaf (C := C) (F := F) k (.stackStoreAny 5 8 : HolProg width) rfl)
          (clockBoundLeaf (C := C) (F := F) k (addBytesInWordInst 8 : HolProg width) rfl))))
  have hbody := clockBoundIte k .notLower 7 (.imm 2) _ _ _ _
    (clockBoundIte k .test 7 (.imm 1) _ _ _ _ ht hf)
    (clockBoundLeaf (C := C) (F := F) k (.break 0 : HolProg width) rfl)
  let body : HolProg width := .ite .notLower 7 (.imm 2)
    (.ite .test 7 (.imm 1) (listSeqHOL [rightShiftInst 7 1, addBytesInWordInst 8])
      (listSeqHOL [.stackLoadAny 5 8, rightShiftInst 7 1, wordGcMoveCode conf,
        .stackStoreAny 5 8, addBytesInWordInst 8])) (.break 0)
  have hb : ClockBound (C := C) (F := F) k body (119 + 12 * (k + 1)) := by
    intro st hs
    have hh := hbody st hs
    change steps (body, st) ≤ _ at hh
    omega
  have hl := clockBoundLoop k body (119 + 12 * (k + 1)) hb
  intro st hs
  have hh := hl st hs
  change steps (wordGcMoveBitmapCode conf, st) ≤ _ at hh
  have heq : 119 + 12 * (k + 1) + 1 = 120 + 12 * (k + 1) := by omega
  rw [heq] at hh
  exact hh

end SteppedFlapjack.StackAllocSteps
