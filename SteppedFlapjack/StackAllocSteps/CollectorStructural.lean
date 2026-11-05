import SteppedFlapjack.StackAllocSteps.GcMoveClock

/-! Structural clock-indexed step bounds for all collector configurations. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Programs whose recursive control flow is limited to loops, branches and sequencing. -/
def loopOnly : HolProg width → Bool
  | .seq a b => loopOnly a && loopOnly b
  | .ite _ _ _ a b => loopOnly a && loopOnly b
  | .loop a => loopOnly a
  | .jumpLower _ _ _ | .rawCall _ | .call _ _ _ => false
  | _ => true

/-- A structural bound for loop-only programs at a given clock limit. -/
def loopOnlyCost (k : Nat) : HolProg width → Nat
  | .seq a b => 1 + loopOnlyCost k a + loopOnlyCost k b
  | .ite _ _ _ a b => 1 + loopOnlyCost k a + loopOnlyCost k b
  | .loop a => (loopOnlyCost k a + 1) * (k + 1)
  | _ => 1

/-- Every loop-only program satisfies its structural clock-indexed bound. -/
theorem loopOnlyCostBound (k : Nat) (p : HolProg width) (h : loopOnly p = true) :
    ClockBound (C := C) (F := F) k p (loopOnlyCost k p) := by
  cases hp : p <;> rw [hp] at h <;> try simp [loopOnly] at h
  case seq a b =>
    exact clockBoundSeq k a b _ _ (loopOnlyCostBound k a h.1) (loopOnlyCostBound k b h.2)
  case ite cmp r ri a b =>
    exact clockBoundIte k cmp r ri a b _ _ (loopOnlyCostBound k a h.1) (loopOnlyCostBound k b h.2)
  case loop a =>
    exact clockBoundLoop k a _ (loopOnlyCostBound k a h)
  all_goals exact clockBoundLeaf k _ rfl
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

@[simp] theorem loopOnlyMemcpy : loopOnly (memcpyCode : HolProg width) = true := by
  simp only [memcpyCode, whileHOL, listSeqHOL, loopOnly, Bool.and_eq_true]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyClearTop (i n : Nat) : loopOnly (clearTopInst i n : HolProg width) = true := by
  rfl

@[simp] theorem loopOnlyGenMove (conf : Config) : loopOnly (wordGenGcMoveCode conf : HolProg width) = true := by
  simp only [wordGenGcMoveCode, listSeqHOL, loopOnly, Bool.and_eq_true, loopOnlyMemcpy, loopOnlyClearTop, true_and]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenPartialMove (conf : Config) : loopOnly (wordGenGcPartialMoveCode conf : HolProg width) = true := by
  simp only [wordGenGcPartialMoveCode, listSeqHOL, loopOnly, Bool.and_eq_true, loopOnlyMemcpy, loopOnlyClearTop, true_and]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenMoveBitmap (conf : Config) : loopOnly (wordGenGcMoveBitmapCode conf : HolProg width) = true := by
  simp [wordGenGcMoveBitmapCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenPartialMoveBitmap (conf : Config) : loopOnly (wordGenGcPartialMoveBitmapCode conf : HolProg width) = true := by
  simp [wordGenGcPartialMoveBitmapCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenMoveBitmaps (conf : Config) : loopOnly (wordGenGcMoveBitmapsCode conf : HolProg width) = true := by
  simp [wordGenGcMoveBitmapsCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenPartialMoveBitmaps (conf : Config) : loopOnly (wordGenGcPartialMoveBitmapsCode conf : HolProg width) = true := by
  simp [wordGenGcPartialMoveBitmapsCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenMoveRootsBitmaps (conf : Config) : loopOnly (wordGenGcMoveRootsBitmapsCode conf : HolProg width) = true := by
  simp [wordGenGcMoveRootsBitmapsCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenPartialMoveRootsBitmaps (conf : Config) : loopOnly (wordGenGcPartialMoveRootsBitmapsCode conf : HolProg width) = true := by
  simp [wordGenGcPartialMoveRootsBitmapsCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenMoveList (conf : Config) : loopOnly (wordGenGcMoveListCode conf : HolProg width) = true := by
  simp [wordGenGcMoveListCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenPartialMoveList (conf : Config) : loopOnly (wordGenGcPartialMoveListCode conf : HolProg width) = true := by
  simp [wordGenGcPartialMoveListCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenMoveData (conf : Config) : loopOnly (wordGenGcMoveDataCode conf : HolProg width) = true := by
  simp [wordGenGcMoveDataCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenPartialMoveRefList (conf : Config) : loopOnly (wordGenGcPartialMoveRefListCode conf : HolProg width) = true := by
  simp [wordGenGcPartialMoveRefListCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenPartialMoveData (conf : Config) : loopOnly (wordGenGcPartialMoveDataCode conf : HolProg width) = true := by
  simp [wordGenGcPartialMoveDataCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenMoveRefs (conf : Config) : loopOnly (wordGenGcMoveRefsCode conf : HolProg width) = true := by
  simp [wordGenGcMoveRefsCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlyGenMoveLoop (conf : Config) : loopOnly (wordGenGcMoveLoopCode conf : HolProg width) = true := by
  simp [wordGenGcMoveLoopCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlySimpleMove (conf : Config) : loopOnly (wordGcMoveCode conf : HolProg width) = true := by
  simp [wordGcMoveCode, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlySimpleMoveList (conf : Config) : loopOnly (wordGcMoveListCode conf : HolProg width) = true := by
  simp [wordGcMoveListCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlySimpleMoveLoop (conf : Config) : loopOnly (wordGcMoveLoopCode conf : HolProg width) = true := by
  simp [wordGcMoveLoopCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlySimpleMoveBitmap (conf : Config) : loopOnly (wordGcMoveBitmapCode conf : HolProg width) = true := by
  simp [wordGcMoveBitmapCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlySimpleMoveBitmaps (conf : Config) : loopOnly (wordGcMoveBitmapsCode conf : HolProg width) = true := by
  simp [wordGcMoveBitmapsCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlySimpleMoveRootsBitmaps (conf : Config) : loopOnly (wordGcMoveRootsBitmapsCode conf : HolProg width) = true := by
  simp [wordGcMoveRootsBitmapsCode, whileHOL, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

@[simp] theorem loopOnlySetNewTrigger (a b : Nat) (gs : List Nat) :
    loopOnly (setNewTrigger a b gs : HolProg width) = true := by
  simp [setNewTrigger, listSeqHOL, loopOnly]
  repeat' (first | rfl | constructor)

/-- Every configured collector program uses only structural control and loops. -/
theorem loopOnlyWordGcCode (conf : Config) : loopOnly (wordGcCode conf : HolProg width) = true := by
  cases hk : conf.gcKind with
  | none =>
    simp [wordGcCode, hk, listSeqHOL, loopOnly]
    all_goals rfl
  | simple =>
    simp [wordGcCode, hk, listSeqHOL, loopOnly]
    repeat' (first | rfl | constructor)
  | generational gs =>
    cases gs <;> simp [wordGcCode, hk, wordGcPartialOrFull, listSeqHOL, loopOnly]
    all_goals repeat' (first | rfl | constructor)

/-- A computed clock-indexed step bound for every collector kind. -/
theorem wordGcCodeStructuralBound (conf : Config) (k : Nat) :
    ClockBound (C := C) (F := F) k (wordGcCode conf : HolProg width)
      (loopOnlyCost k (wordGcCode conf : HolProg width)) :=
  loopOnlyCostBound k _ (loopOnlyWordGcCode (width := width) conf)

end SteppedFlapjack.StackAllocSteps
