import SteppedFlapjack.StackAllocSteps.GcMoveRootsClock
import SteppedFlapjack.StackAllocSteps.GcMoveLoopClock

/-! Step bounds for the complete simple-collector allocation code. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A bounded list of programs has a bounded sequential execution. -/
theorem clockBoundListSeq (k M : Nat) (hm : 1 ≤ M) (ps : List (HolProg width))
    (hp : ∀ p ∈ ps, ClockBound (C := C) (F := F) k p M) :
    ClockBound (C := C) (F := F) k (listSeqHOL ps) ((2 * ps.length + 1) * M) := by
  induction ps with
  | nil =>
    simp only [listSeqHOL, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.one_mul]
    intro s hs
    have h := steps_leaf (.skip : HolProg width) s rfl
    omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      simp only [listSeqHOL, List.length_cons, List.length_nil, Nat.mul_zero, Nat.zero_add] at *
      intro s hs
      have h := hp a (by simp) s hs
      omega
    | cons b ys =>
      have ha := hp a (by simp)
      have hb : ∀ p ∈ b :: ys, ClockBound (C := C) (F := F) k p M := by
        intro p hin; exact hp p (by simp [hin])
      have ht := ih hb
      have h := clockBoundSeq k a (listSeqHOL (b :: ys)) M ((2 * (b :: ys).length + 1) * M) ha ht
      intro s hs
      have hrun := h s hs
      simp only [listSeqHOL, List.length_cons] at hrun ⊢
      nlinarith

/-- An assembled bound for the simple collector allocation program. -/
theorem simpleGcClockBound (k : Nat) (conf : Config) (hk : conf.gcKind = .simple) :
    let G := 100 + 12 * (k + 1)
    let R := ((((120 + 12 * (k + 1)) * (k + 1) + 20) * (k + 1)) + 20) * (k + 1)
    let L := ((111 + 12 * (k + 1)) * (k + 1) + 25) * (k + 1)
    ClockBound (C := C) (F := F) k (wordGcCode conf : HolProg width) (73 * (10 + G + R + L)) := by
  dsimp only
  let G := 100 + 12 * (k + 1)
  let R := ((((120 + 12 * (k + 1)) * (k + 1) + 20) * (k + 1)) + 20) * (k + 1)
  let L := ((111 + 12 * (k + 1)) * (k + 1) + 25) * (k + 1)
  let M := 10 + G + R + L
  have hm : 1 ≤ M := by dsimp [M]; omega
  let ps : List (HolProg width) := [.set .allocSize 1,
         .set .nextFree 0,
         constInst 1 0,
         moveHOL 2 1,
         .get 3 .otherHeap,
         moveHOL 4 1,
         .get 5 .globals,
         moveHOL 6 1,
         moveHOL 8 1,
         wordGcMoveCode conf,
         .set .globals 5,
         moveHOL 7 5,
         rightShiftInst 7 (shiftLength conf),
         leftShiftInst 7 (wordShiftAmount width),
         .get 9 .otherHeap,
         addInst 7 9,
         .set .globReal 7,
         constInst 7 0,
         .stackLoadAny 9 8,
         moveHOL 8 7,
         wordGcMoveRootsBitmapsCode conf,
         .get 8 .otherHeap,
         wordGcMoveLoopCode conf,
         .get 0 .currHeap,
         .get 1 .otherHeap,
         .get 2 .heapLength,
         addInst 2 1,
         .set .currHeap 1,
         .set .otherHeap 0,
         .get 0 .nextFree,
         .set .nextFree 8,
         .set .endOfHeap 2,
         .set .triggerGC 2,
         .get 1 .allocSize,
         subInst 2 8,
         .ite .lower 2 (.reg 1) (.seq (constInst 1 1) (.halt 1)) .skip]
  have hp : ∀ p ∈ ps, ClockBound (C := C) (F := F) k p M := by
    intro p hp
    simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact clockBoundWeaken k _ 1 M (clockBoundLeaf k _ rfl) (by dsimp [M]; omega)
      | exact clockBoundWeaken k _ G M (gcMoveClockBound k conf) (by dsimp [M]; omega)
      | exact clockBoundWeaken k _ R M (gcMoveRootsClockBound k conf) (by dsimp [M]; omega)
      | exact clockBoundWeaken k _ L M (gcMoveLoopClockBound k conf) (by dsimp [M]; omega)
      | (have h := clockBoundIte k .lower 2 (.reg 1) _ _ _ _
           (clockBoundSeq k _ _ _ _ (clockBoundLeaf (C := C) (F := F) k (constInst 1 1 : HolProg width) rfl)
             (clockBoundLeaf (C := C) (F := F) k (.halt 1 : HolProg width) rfl))
           (clockBoundLeaf (C := C) (F := F) k (.skip : HolProg width) rfl)
         exact clockBoundWeaken k _ 5 M h (by dsimp [M]; omega))
  have hh := clockBoundListSeq k M hm ps hp
  intro st hs
  have hh := hh st hs
  change steps (wordGcCode conf, st) ≤ _
  simp only [wordGcCode, hk]
  change steps (listSeqHOL ps, st) ≤ 73 * M
  simpa [ps] using hh

end SteppedFlapjack.StackAllocSteps
