import SteppedFlapjack.StackAllocSteps.GcMoveClock

/-! A step bound for the simple collector heap traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

set_option maxHeartbeats 2000000 in
/-- A clock-based bound for the heap traversal loop. -/
theorem gcMoveLoopClockBound (k : Nat) (conf : Config) :
    ClockBound (C := C) (F := F) k (wordGcMoveLoopCode conf : HolProg width)
      (((111 + 12 * (k + 1)) * (k + 1) + 25) * (k + 1)) := by
  let L := (111 + 12 * (k + 1)) * (k + 1)
  have ht := clockBoundSeq k _ _ _ _
    (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 7 (width - conf.lenSize) : HolProg width) rfl)
    (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (addBytesInWordInst 8 : HolProg width) rfl)
      (gcMoveListClockBound (C := C) (F := F) (width := width) k conf))
  have hf := clockBoundSeq k _ _ _ _
    (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 7 (width - conf.lenSize) : HolProg width) rfl)
    (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (add1Inst 7 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
        (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 7 (wordShiftAmount width) : HolProg width) rfl)
        (clockBoundLeaf (C := C) (F := F) k (addInst 8 7 : HolProg width) rfl)))
  have hm := clockBoundSeq k _ _ _ _
    (clockBoundLeaf (C := C) (F := F) k (loadInst 7 8 : HolProg width) rfl)
    (clockBoundIte k .test 7 (.imm 4) _ _ _ _ ht hf)
  have hbody := clockBoundIte k .notEqual 3 (.reg 8) _ _ _ _ hm
    (clockBoundLeaf (C := C) (F := F) k (.break 0 : HolProg width) rfl)
  let body : HolProg width := .ite .notEqual 3 (.reg 8)
    (listSeqHOL [loadInst 7 8, .ite .test 7 (.imm 4)
      (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), addBytesInWordInst 8, wordGcMoveListCode conf])
      (listSeqHOL [rightShiftInst 7 (width - conf.lenSize), add1Inst 7,
        leftShiftInst 7 (wordShiftAmount width), addInst 8 7])]) (.break 0)
  have hb : ClockBound (C := C) (F := F) k body (L + 24) := by
    intro st hs
    have hh := hbody st hs
    change steps (body, st) ≤ _ at hh
    change steps (body, st) ≤
      1 + (1 + 1 + (1 + (1 + 1 + (1 + 1 + L)) + (1 + 1 + (1 + 1 + (1 + 1 + 1))))) + 1 at hh
    omega
  have hl := clockBoundLoop k body (L + 24) hb
  intro st hs
  have hh := hl st hs
  change steps (wordGcMoveLoopCode conf, st) ≤ _ at hh
  have heq : L + 24 + 1 = L + 25 := by omega
  rw [heq] at hh
  exact hh

end SteppedFlapjack.StackAllocSteps
