import SteppedFlapjack.StackAllocSteps.GcMoveBitmapsClock

/-! A clock-based step bound for the simple collector root traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A clock-based bound for the collector root traversal. -/
theorem gcMoveRootsClockBound (k : Nat) (conf : Config) :
    ClockBound (C := C) (F := F) k (wordGcMoveRootsBitmapsCode conf : HolProg width)
      (((((120 + 12 * (k + 1)) * (k + 1) + 20) * (k + 1)) + 20) * (k + 1)) := by
  let B := ((120 + 12 * (k + 1)) * (k + 1) + 20) * (k + 1)
  have ht := clockBoundSeq k _ _ _ _
    (clockBoundLeaf (C := C) (F := F) k (moveHOL 0 9 : HolProg width) rfl)
    (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (sub1Inst 9 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
        (clockBoundLeaf (C := C) (F := F) k (addBytesInWordInst 8 : HolProg width) rfl)
        (clockBoundSeq k _ _ _ _ (gcMoveBitmapsClockBound (C := C) (F := F) (width := width) k conf)
          (clockBoundLeaf (C := C) (F := F) k (.stackLoadAny 9 8 : HolProg width) rfl))))
  have hbody := clockBoundIte k .notTest 9 (.reg 9) _ _ _ _ ht
    (clockBoundLeaf (C := C) (F := F) k (.break 0 : HolProg width) rfl)
  let body : HolProg width := .ite .notTest 9 (.reg 9)
    (listSeqHOL [moveHOL 0 9, sub1Inst 9, addBytesInWordInst 8,
      wordGcMoveBitmapsCode conf, .stackLoadAny 9 8]) (.break 0)
  have hb : ClockBound (C := C) (F := F) k body (B + 19) := by
    intro st hs
    have hh := hbody st hs
    change steps (body, st) ≤ _ at hh
    change steps (body, st) ≤ 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + B + 1)))) + 1 at hh
    omega
  have hl := clockBoundLoop k body (B + 19) hb
  intro st hs
  have hh := hl st hs
  change steps (wordGcMoveRootsBitmapsCode conf, st) ≤ _ at hh
  have heq : B + 19 + 1 = B + 20 := by omega
  rw [heq] at hh
  exact hh

end SteppedFlapjack.StackAllocSteps
