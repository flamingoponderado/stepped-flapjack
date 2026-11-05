import SteppedFlapjack.StackRawCallSteps.EntrySteps
import SteppedFlapjack.StackAllocSteps.EntrySteps
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord SteppedFlapjack.StackSteps

/-- The raw-call optimization followed by stack allocation preserves an entry
run with the stack-allocation factor. -/
theorem rawCallAllocEntryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (anything : WordSemGcFun width) (cr : CompileFn width C) (c : Config) (hwidth : 8 ≤ width)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : evaluate ((.call none (.inl start) none : HolProg width), {source with clock := clock}) = (result, post))
    (nonError : result ≠ some .error)
    (pre : Pre cr c {source with code := sptFromAList (StackRawCall.compile code), clock := clock} source.regs) :
    ∃ rawClock rawPost allocClock regs,
      evaluate ((.call none (.inl start) none : HolProg width),
        Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile code), clock := clock + rawClock}
          allocClock source.regs) = (result, Res anything cr c rawPost regs) ∧
      rawPost.ffi = post.ffi ∧
      steps ((.call none (.inl start) none : HolProg width),
        Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile code), clock := clock + rawClock}
          allocClock source.regs) ≤
      uniformFactor (width := width) c * steps ((.call none (.inl start) none : HolProg width),
        {source with clock := clock}) := by
  obtain ⟨rawClock, rawPost, rawRun, ffiEq, rawCost⟩ :=
    SteppedFlapjack.StackRawCallSteps.entryWithinSteps code source start clock result post distinct sourceCode run nonError
  let rawState : StackSemStateFiniteExact width C F :=
    {source with code := sptFromAList (StackRawCall.compile code), clock := clock + rawClock}
  have pre' : Pre cr c rawState rawState.regs :=
    ⟨pre.code, pre.oracle, pre.gcFun, pre.useAlloc, pre.stack, pre.regs, pre.useStack, pre.buf, pre.compile⟩
  obtain ⟨allocClock, regs, allocRun, allocCost⟩ :=
    compileEntryWithinSteps anything cr c hwidth start rawState rawPost result rawRun nonError pre'
  refine ⟨rawClock, rawPost, allocClock, regs, allocRun, ffiEq, ?_⟩
  exact allocCost.trans (Nat.mul_le_mul_left _ rawCost)
end SteppedFlapjack.StackAllocSteps
