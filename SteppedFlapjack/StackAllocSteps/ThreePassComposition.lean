import SteppedFlapjack.StackAllocSteps.RawCallComposition
import SteppedFlapjack.StackRemoveSteps.EntrySteps
import Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
import Flapjack.Compiler.Backend.LabToTarget.StateTransport
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps SteppedFlapjack.StackRemoveSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- The allocation precondition is independent of the source clock. -/
theorem pre_setClock {width : Nat} [NeZero width] {C F : Type}
    (cr : CompileFn width C) (c : Config) (source : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) (clock : Nat)
    (pre : Pre cr c source regs) : Pre cr c {source with clock := clock} regs := by
  obtain ⟨code,oracle,gc,useAlloc,stack,registers,useStack,buf,compile⟩ := pre
  exact ⟨code,oracle,gc,useAlloc,stack,registers,useStack,buf,compile⟩

/-- Stack removal retains its state relation when both clocks are reset to the
same replay budget. -/
theorem removeStateRel_setClocks {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (clock : Nat)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer {source with clock := clock} {target with clock := clock} := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,_,rest⟩ := relation
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,rfl,rest⟩

/-- The Stack-to-Lab initial relation can be synchronized to the same replay
clock without changing either program or machine data. -/
theorem stackLabStateRel_setClocks {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (target : LabSem.State width C F)
    (clock : Nat) (relation : StackToLab.Proofs.StateRel.stateRel source target) :
    StackToLab.Proofs.StateRel.stateRel {source with clock := clock} {target with clock := clock} := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,_,rest⟩ := relation
  exact ⟨h1,h2,h3,h4,h5,h6,h7,rfl,rest⟩

/-- Reuse an initialized Stack-to-machine pipeline at any source replay clock.
The same clock is installed in the Stack-removal target and Lab states; the
machine, code and oracle witnesses remain unchanged. -/
theorem pipelineInitial_setClock {width : Nat} [NeZero width] {S Q F : Type}
    (source target : StackSemStateFiniteExact width LabToTarget.Config F)
    (lab : LabSem.State width LabToTarget.Config F)
    (anything : WordSemGcFun width) (cr : CompileFn width LabToTarget.Config) (c : Config)
    (regs : HolFiniteMapExact Nat (WordLocW width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer oldClock newClock : Nat)
    (mc : MachineConfig width S Q) (machine : S)
    (labCode : LabSem.LabProgHOL width) (labs : Spt (Spt Nat)) (pc : BitVec width)
    (asm : AsmState width)
    (pre : Pre cr c {source with clock := oldClock} regs)
    (removeRel : stateRelHOL jump bounds pointer
      (Tgt anything cr c {source with clock := oldClock} 0 regs) target)
    (labRel : StackToLab.Proofs.StateRel.stateRel target lab)
    (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    Pre cr c {source with clock := newClock} regs ∧
    stateRelHOL jump bounds pointer (Tgt anything cr c {source with clock := newClock} 0 regs)
      {target with clock := newClock} ∧
    StackToLab.Proofs.StateRel.stateRel {target with clock := newClock} {lab with clock := newClock} ∧
    LabToTarget.oracleTie mc machine {lab with clock := newClock} ∧
    LabToTarget.stateRel (mc,labCode,labs,pc) {lab with clock := newClock} asm machine := by
  refine ⟨?_,?_,stackLabStateRel_setClocks target lab newClock labRel,?_,?_⟩
  · exact pre_setClock cr c {source with clock := oldClock} regs newClock pre
  · simpa only [Tgt, Nat.add_zero] using
      removeStateRel_setClocks jump bounds pointer
        (Tgt anything cr c {source with clock := oldClock} 0 regs) target newClock removeRel
  · exact LabToTarget.oracleTie_clock mc machine lab newClock tie
  · exact (LabToTarget.stateRel_clock (mc,labCode,labs,pc) lab asm machine newClock).mpr machineRel

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
