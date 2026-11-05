import SteppedFlapjack.StackAllocSteps.CompCorrect
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord SteppedFlapjack.StackSteps

/-- The compiled entry call preserves the result and FFI state, with a
collector-dependent multiplicative bound on fine-grained steps. -/
theorem compileEntryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C) (c : Config) (hwidth : 8 ≤ width)
    (start : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate (.call none (.inl start) none, s) = (r, t)) (hr : r ≠ some .error)
    (hpre : Pre cr c s s.regs) :
    ∃ ck regs1,
      evaluate (.call none (.inl start) none, Tgt anything cr c s ck s.regs) =
        (r, Res anything cr c t regs1) ∧
      steps (.call none (.inl start) none, Tgt anything cr c s ck s.regs) ≤
        uniformFactor (width := width) c * steps (.call none (.inl start) none, s) := by
  obtain ⟨ck, regs1, he, _, hs⟩ :=
    compCorrectWithinSteps anything cr c hwidth (.call none (.inl start) none) s
      r t 0 0 s.regs h hr (by simp [Flapjack.Compiler.Backend.StackProps.allocArg]) hpre
  exact ⟨ck, regs1, he, hs⟩

end SteppedFlapjack.StackAllocSteps
