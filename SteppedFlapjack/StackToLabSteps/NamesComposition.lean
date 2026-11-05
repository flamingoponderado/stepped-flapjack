import SteppedFlapjack.StackNamesSteps.Semantics
import SteppedFlapjack.StackToLabSteps.GeneratedHaltSteps
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackNames
open SteppedFlapjack.StackSteps SteppedFlapjack.StackNamesSteps

/-- Renaming followed by flattening preserves a bounded entry run, with the
generated halt procedure's four-step cost discharged. -/
theorem namesFlattenGeneratedWithin {width : Nat} [NeZero width] {C F : Type}
    (f : Spt Nat) (jump : Bool) (off : BitVec width × BitVec width)
    (gen : Bool) (maxHeap a b : Nat) (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F) (lab : Flapjack.Compiler.Backend.LabSem.State width C F)
    (start k n : Nat) (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : s.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump off gen maxHeap a b code)))
    (hor : s.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel s lab)
    (hpc : Flapjack.Compiler.Backend.LabSem.locToPc start 0 lab.code = some lab.pc)
    (run : evaluate ((.call none (.inl start) none : HolProg width),
      {makeInit f (sptFromAList (StackRemove.compileHOL jump off gen maxHeap a b code)) oracle s with clock := k}) =
      (res, post))
    (hsteps : steps ((.call none (.inl start) none : HolProg width),
      {makeInit f (sptFromAList (StackRemove.compileHOL jump off gen maxHeap a b code)) oracle s with clock := k}) ≤ n)
    (hres : stackEntryClass res = .CompleteResult outcome) :
    ∃ m ≤ flattenStepFactor * (n + 4), ∃ labPost,
      Flapjack.Compiler.Backend.LabSem.evaluate {lab with clock := m} = (.halt outcome, labPost) ∧
      labPost.ffi.ioEvents = post.ffi.ioEvents := by
  obtain ⟨renamedPost, renamedRun, renamedSteps, postEq⟩ :=
    stackNamesSemanticsWithin ha hs hk hf hcode hor run hsteps
  obtain ⟨m, hm, labPost, labRun, events⟩ :=
    flattenGeneratedWithin f jump off gen maxHeap a b code hcode rel hpc renamedRun renamedSteps hres
  refine ⟨m, hm, labPost, labRun, ?_⟩
  rw [events, postEq]
  rfl
end SteppedFlapjack.StackToLabSteps
