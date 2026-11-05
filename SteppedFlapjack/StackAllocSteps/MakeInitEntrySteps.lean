import SteppedFlapjack.StackAllocSteps.EntrySteps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.MakeInit
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord SteppedFlapjack.StackSteps
open Flapjack.Compiler.Backend.StackAlloc.ProgCompSupport

/-- Stack allocation's actual make-init state simulates a bounded entry run
from the compiled state, with the uniform collector factor. -/
theorem makeInitEntryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F) (c : Config) (hwidth : 8 ≤ width) (start k n : Nat)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (hcode : ∀ key prog, sptAListLookup key code = some prog → key ≠ gcStubLocation ∧ StackProps.allocArg prog)
    (horacle : ∀ i key prog, (key, prog) ∈ (oracle i).2.1 → key ≠ gcStubLocation ∧ StackProps.allocArg prog)
    (hstack : s.useStack = true) (hstore : s.useStore = true) (halloc : s.useAlloc = false)
    (scode : s.code = sptFromAList (compile c code))
    (soracle : s.compileOracle = Prod.map id (Prod.map (List.map progComp) id) ∘ oracle)
    (hbuf : s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1)
    (hst : s.stack.length * (width / 8) < 2 ^ width)
    (run : evaluate ((.call none (.inl start) none : HolProg width),
      {StackAlloc.makeInit c (sptFromAList code) oracle s with clock := k}) = (result, post))
    (nonError : result ≠ some .error)
    (hsteps : steps ((.call none (.inl start) none : HolProg width),
      {StackAlloc.makeInit c (sptFromAList code) oracle s with clock := k}) ≤ n) :
    ∃ extra targetPost,
      evaluate ((.call none (.inl start) none : HolProg width), {s with clock := k + extra}) =
        (result, targetPost) ∧ targetPost.ffi = post.ffi ∧
      steps ((.call none (.inl start) none : HolProg width), {s with clock := k + extra}) ≤
        uniformFactor (width := width) c * n := by
  let source := {StackAlloc.makeInit c (sptFromAList code) oracle s with clock := k}
  have pre : Pre s.compile c source source.regs := by
    refine ⟨?_, ?_, rfl, rfl, ?_, ?_, rfl, ?_, rfl⟩
    · intro key prog h
      apply hcode key prog
      simpa [source, StackAlloc.makeInit, sptLookup_sptFromAList] using h
    · exact horacle
    · exact hst
    · intro key value hv
      exact hv
    · exact hbuf
  obtain ⟨extra, regs, targetRun, targetCost⟩ :=
    compileEntryWithinSteps s.gcFun s.compile c hwidth start source post result run nonError pre
  have hcc : sptFromAList (compile c (sptToAList (sptFromAList code))) = s.code := by
    rw [scode]
    refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun key => ?_
    rw [CompCorrect.sptLookup_compile, CompCorrect.sptLookup_compile,
      sptAListLookup_sptToAList, sptLookup_sptFromAList]
  have targetEq : Tgt s.gcFun s.compile c source extra source.regs = {s with clock := k + extra} := by
    simp [source, Tgt, StackAlloc.makeInit, hstack, hstore, halloc, hcc, soracle]
  rw [targetEq] at targetRun targetCost
  refine ⟨extra, Res s.gcFun s.compile c post regs, targetRun, rfl, ?_⟩
  exact targetCost.trans (Nat.mul_le_mul_left _ hsteps)
end SteppedFlapjack.StackAllocSteps
