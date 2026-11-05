import SteppedFlapjack.StackAllocSteps.GcMoveBitmapClock

/-! Clock-based step bounds for collector bitmap-list traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A clock-based bound for the bitmap-list traversal. -/
theorem gcMoveBitmapsClockBound (k : Nat) (conf : Config) :
    ClockBound (C := C) (F := F) k (wordGcMoveBitmapsCode conf : HolProg width)
      (((120 + 12 * (k + 1)) * (k + 1) + 20) * (k + 1)) := by
  let B := (120 + 12 * (k + 1)) * (k + 1)
  have ht := clockBoundSeq k _ _ _ _
    (clockBoundLeaf (C := C) (F := F) k (.bitmapLoad 7 9 : HolProg width) rfl)
    (clockBoundSeq k _ _ _ _ (gcMoveBitmapClockBound (C := C) (F := F) (width := width) k conf)
      (clockBoundSeq k _ _ _ _
        (clockBoundLeaf (C := C) (F := F) k (.bitmapLoad 0 9 : HolProg width) rfl)
        (clockBoundSeq k _ _ _ _
          (clockBoundLeaf (C := C) (F := F) k (add1Inst 9 : HolProg width) rfl)
          (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 0 (width - 1) : HolProg width) rfl))))
  have hbody := clockBoundIte k .notTest 0 (.reg 0) _ _ _ _ ht
    (clockBoundLeaf (C := C) (F := F) k (.break 0 : HolProg width) rfl)
  let body : HolProg width := .ite .notTest 0 (.reg 0)
    (listSeqHOL [.bitmapLoad 7 9, wordGcMoveBitmapCode conf, .bitmapLoad 0 9, add1Inst 9,
      rightShiftInst 0 (width - 1)]) (.break 0)
  have hb : ClockBound (C := C) (F := F) k body (B + 19) := by
    intro st hs
    have hh := hbody st hs
    change steps (body, st) ≤ _ at hh
    change steps (body, st) ≤ 1 + (1 + 1 + (1 + B + (1 + 1 + (1 + 1 + 1)))) + 1 at hh
    omega
  have hl := clockBoundLoop k body (B + 19) hb
  intro st hs
  have hh := hl st hs
  change steps (wordGcMoveBitmapsCode conf, st) ≤ _ at hh
  have heq : B + 19 + 1 = B + 20 := by omega
  rw [heq] at hh
  exact hh

end SteppedFlapjack.StackAllocSteps
