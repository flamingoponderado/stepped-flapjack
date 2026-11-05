import SteppedFlapjack.StackAllocSteps.GenMoveLoopCorrect
import SteppedFlapjack.StackAllocSteps.BoundedNormal

/-! A fuel-based step bound for the full generational collector loop. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Full generational collection has a fuel-based step bound. -/
theorem genGcMoveLoopStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord)
    (old : BitVec width) :
    ∀ (k : Nat) (s : StackSemStateFiniteExact width C F)
      (pax i pa ib pb pbx tt i1 pa1 ib1 pb1 : BitVec width)
      (m1 : BitVec width → WordLocW width),
      wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, s.memory, s.mdomain) =
        (i1, pa1, ib1, pb1, m1, true) →
      GenLoopReady s pax i pa ib pb pbx old tt → steps (wordGenGcMoveLoopCode conf, s) ≤ loopOnlyCost (k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) (wordGenGcMoveLoopCode conf : HolProg width) := by
  intro k s pax i pa ib pb pbx tt i1 pa1 ib1 pb1 m1 h r
  let zero := {s with clock := 0}
  have rz : GenLoopReady zero pax i pa ib pb pbx old tt := by
    cases r
    constructor <;> assumption
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hck, hrun⟩ :=
    genGcMoveLoopBoundedClock hsl hws hw2 hlen hshift old k zero pax i pa ib pb pbx tt
      i1 pa1 ib1 pb1 m1 h rz
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenMoveLoop conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh


end SteppedFlapjack.StackAllocSteps
