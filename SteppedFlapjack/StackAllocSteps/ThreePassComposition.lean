import SteppedFlapjack.StackAllocSteps.RawCallComposition
import SteppedFlapjack.StackRemoveSteps.EntrySteps
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps SteppedFlapjack.StackRemoveSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- Compose raw-call optimization, stack allocation, and stack removal on an
entry run with a supplied source-step upper bound. -/
theorem threePassEntryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source target : StackSemStateFiniteExact width C F)
    (start clock n : Nat) (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (anything : WordSemGcFun width) (cr : CompileFn width C) (c : Config) (hwidth : 8 ≤ width)
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : evaluate ((.call none (.inl start) none : HolProg width), {source with clock := clock}) = (result, post))
    (nonError : result ≠ some .error)
    (sourceSteps : steps ((.call none (.inl start) none : HolProg width), {source with clock := clock}) ≤ n)
    (pre : Pre cr c {source with code := sptFromAList (StackRawCall.compile code), clock := clock} source.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile code), clock := clock} 0 source.regs)
      target) :
    ∃ rawClock allocClock removeClock finalPost,
      evaluate ((.call none (.inl start) none : HolProg width),
        {target with clock := removeClock + (clock + rawClock + allocClock)}) = (result, finalPost) ∧
      finalPost.ffi = post.ffi ∧
      steps ((.call none (.inl start) none : HolProg width),
        {target with clock := removeClock + (clock + rawClock + allocClock)}) ≤
      computedRunCost bounds (uniformFactor (width := width) c * n) (.call none (.inl start) none)
        (Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile code), clock := clock} 0 source.regs) *
        (uniformFactor (width := width) c * n) := by
  obtain ⟨rawClock, rawPost, allocClock, regs, allocRun, ffiEq, allocCost⟩ :=
    rawCallAllocEntryWithinSteps code source start clock result post anything cr c hwidth distinct sourceCode run nonError pre
  let allocBase := Tgt anything cr c
    {source with code := sptFromAList (StackRawCall.compile code), clock := clock} 0 source.regs
  have allocRun' : evaluate ((.call none (.inl start) none : HolProg width),
      {allocBase with clock := clock + rawClock + allocClock}) = (result, Res anything cr c rawPost regs) := by
    simpa [allocBase, Tgt] using allocRun
  have allocSteps : steps ((.call none (.inl start) none : HolProg width),
      {allocBase with clock := clock + rawClock + allocClock}) ≤ uniformFactor (width := width) c * n := by
    apply Nat.le_trans ?_ (Nat.mul_le_mul_left _ sourceSteps)
    simpa [allocBase, Tgt] using allocCost
  obtain ⟨removeClock, finalPost, removeRun, removeFfi, removeCost⟩ :=
    SteppedFlapjack.StackRemoveSteps.entryWithinSteps jump bounds pointer start (clock + rawClock + allocClock)
      (uniformFactor (width := width) c * n) allocBase target (Res anything cr c rawPost regs) result
      relation allocRun' nonError allocSteps
  exact ⟨rawClock, allocClock, removeClock, finalPost, removeRun, removeFfi.trans ffiEq, removeCost⟩
end SteppedFlapjack.StackAllocSteps
