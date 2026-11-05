import SteppedFlapjack.StackAllocSteps.CallReturnSteps
import SteppedFlapjack.StackAllocSteps.UniformLeaf

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.DataToWord
open SteppedFlapjack.StackSteps

/-- Stack allocation preserves execution with one configuration-dependent
step factor for all terminating, non-error runs on at least byte-wide words. -/
theorem boundedAll {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C) (c : Config) (hwidth : 8 ≤ width) :
    ∀ (mm : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = mm → BoundedGoal anything cr (uniformFactor (width := width) c) c p s := by
  intro mm
  induction mm using EvaluateAddClock.lexNat_wf.induction with
  | _ mm ih =>
  intro p s hm
  subst hm
  have ihp : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure p s) →
      BoundedGoal anything cr (uniformFactor (width := width) c) c q u :=
    fun q u hlt => ih _ hlt q u rfl
  cases p with
  | seq a b => exact boundedSeq anything cr _ (uniformFactorPositive c) c s a b ihp
  | ite cmp r ri a b => exact boundedIte anything cr _ (uniformFactorPositive c) c s cmp r ri a b ihp
  | loop body => exact boundedLoop anything cr _ (uniformFactorPositive c) c s body ihp
  | jumpLower r1 r2 dest => exact boundedJumpLower anything cr _ (uniformFactorPositive c) c s r1 r2 dest ihp
  | rawCall dest => exact boundedRawCall anything cr _ (uniformFactorPositive c) c s dest ihp
  | call ret dest handler =>
      rcases ret with _ | ⟨retH, link, l1, l2⟩
      · exact boundedCallNone anything cr _ (uniformFactorPositive c) c s dest handler ihp
      · exact boundedCallSome anything cr _ (uniformFactorPositive c) c s retH link l1 l2 dest handler ihp
  | _ => exact boundedLeafUniformGoal anything cr c hwidth _ s rfl

/-- Quantitative stack-allocation correctness with a uniform step factor. -/
theorem compCorrectWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C) (c : Config) (hwidth : 8 ≤ width)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    BoundedGoal anything cr (uniformFactor (width := width) c) c p s :=
  boundedAll anything cr c hwidth _ p s rfl

end SteppedFlapjack.StackAllocSteps
