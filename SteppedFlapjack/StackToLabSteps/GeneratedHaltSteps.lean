import SteppedFlapjack.StackToLabSteps.FlattenSemantics
import Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open SteppedFlapjack.StackSteps

/-- The generated halt procedure takes at most four StackSem steps. -/
theorem generatedHaltStepsWithin {width : Nat} [NeZero width] {C F : Type}
    (f : Spt Nat) (jump : Bool) (off : BitVec width × BitVec width)
    (gen : Bool) (maxHeap k l : Nat) (code : List (Nat × HolProg width)) :
    haltStepsWithin C F (sptFromAList (StackNames.compileHOL f
      (StackRemove.compileHOL jump off gen maxHeap k l code))) 4 := by
  intro s ⟨hsub, h0⟩
  have h1 : sptLookup 1 (sptFromAList (StackNames.compileHOL f
      (StackRemove.compileHOL jump off gen maxHeap k l code))) =
      some (StackNames.progCompHOL f (StackRemove.haltInst (0 : BitVec width))) := by
    simp [sptLookup_sptFromAList, StackNames.compileHOL, StackRemove.compileHOL,
      StackRemove.initStubs, StackNames.progCompEntryHOL, sptAListLookup]
  obtain ⟨-, hl⟩ := hsub 1 ((sptMem_iff_lookup _ _).2 ⟨_, h1⟩)
  rw [h1] at hl
  rw [steps_call_none]
  simp only [findCode, hl, if_neg h0, StackRemove.haltInst, StackNames.progCompHOL,
    StackNames.instFindNameHOL, steps_seq]
  rw [steps_leaf _ _ rfl]
  have hh : ∀ st : StackSemStateFiniteExact width C F,
      steps (.halt (StackNames.findNameSpt f 1), st) = 1 := fun _ => steps_leaf _ _ rfl
  split <;> simp [hh]

/-- For generated code, bounded flattening needs no separate halting-cost
hypothesis: the generated halt procedure contributes at most four steps. -/
theorem flattenGeneratedWithin {width : Nat} [NeZero width] {C F : Type} {start k n : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {res : Option (StackSemResult width)} {s' : StackSemStateFiniteExact width C F} {o : HolOutcome}
    (f : Spt Nat) (jump : Bool) (off : BitVec width × BitVec width)
    (gen : Bool) (maxHeap a b : Nat) (code : List (Nat × HolProg width))
    (hcode : s1.code = sptFromAList (StackNames.compileHOL f
      (StackRemove.compileHOL jump off gen maxHeap a b code)))
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel s1 s2)
    (hpc : Flapjack.Compiler.Backend.LabSem.locToPc start 0 s2.code = some s2.pc)
    (ev : evaluate ((.call none (.inl start) none : HolProg width), {s1 with clock := k}) = (res, s'))
    (hn : steps ((.call none (.inl start) none : HolProg width), {s1 with clock := k}) ≤ n)
    (hres : stackEntryClass res = .CompleteResult o) :
    ∃ m ≤ flattenStepFactor * (n + 4), ∃ t',
      Flapjack.Compiler.Backend.LabSem.evaluate {s2 with clock := m} = (.halt o, t') ∧
      t'.ffi.ioEvents = s'.ffi.ioEvents := by
  have hhalt : haltAssum C F s1.code := by
    rw [hcode]
    exact MakeInit.haltAssumLemma
  have hcost : haltStepsWithin C F s1.code 4 := by
    rw [hcode]
    exact generatedHaltStepsWithin f jump off gen maxHeap a b code
  exact flattenSemanticsWithin hhalt rel hpc (fun _ => hcost) ev hn hres

end SteppedFlapjack.StackToLabSteps
