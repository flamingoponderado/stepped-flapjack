import SteppedFlapjack.StackRawCallSteps.CompCorrect
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileSemantics
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CompileSemantics
open SteppedFlapjack.StackSteps

/-- The compiled entry call preserves its result and FFI state without
increasing its fine-grained step count. -/
theorem entryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : evaluate ((.call none (.inl start) none : HolProg width), {source with clock := clock}) = (result, post))
    (nonError : result ≠ some .error) :
    ∃ extra targetPost, evaluate ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) = (result, targetPost) ∧
      targetPost.ffi = post.ffi ∧
      steps ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) ≤
      steps ((.call none (.inl start) none : HolProg width), {source with clock := clock}) := by
  have relation := initialRelation code {source with clock := clock} distinct sourceCode
  obtain ⟨extra, targetPost, space, postRelation, targetRun, _, cost⟩ :=
    (compCorrectWithinSteps (.call none (.inl start) none) {source with clock := clock}
      {source with clock := clock, code := sptFromAList (compile code)} post
      (collectInfo code .ln) result ⟨run, nonError, relation⟩).2
  refine ⟨extra, {targetPost with stackSpace := space}, ?_, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · obtain ⟨_, _, equality, _⟩ := postRelation
    subst targetPost
    rfl
  · simpa only [comp] using cost
end SteppedFlapjack.StackRawCallSteps
