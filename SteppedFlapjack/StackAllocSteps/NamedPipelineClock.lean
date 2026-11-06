import SteppedFlapjack.StackAllocSteps.ThreePassComposition
import Flapjack.Compiler.Backend.StackNames.Proofs.MakeInit

/-! Clock synchronization through the actual StackNames initialization. -/
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.StackRemove

/-- Reclock the initialized backend while retaining StackNames makeInit.
The named Stack state, Lab state and source allocation state receive the same
clock, so a source-derived replay budget can be chosen after initialization. -/
theorem namedPipelineInitial_setClock {width : Nat} [NeZero width] {S Q F : Type}
    (source renamed : StackSemStateFiniteExact width LabToTarget.Config F)
    (lab : LabSem.State width LabToTarget.Config F)
    (anything : WordSemGcFun width) (cr : CompileFn width LabToTarget.Config) (c : Config)
    (regs : HolFiniteMapExact Nat (WordLocW width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer oldClock newClock : Nat)
    (f : Spt Nat) (code : Spt (HolProg width))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg width) × List (BitVec width))
    (mc : MachineConfig width S Q) (machine : S)
    (labCode : LabSem.LabProgHOL width) (labs : Spt (Spt Nat)) (pc : BitVec width) (asm : AsmState width)
    (pre : Pre cr c {source with clock := oldClock} regs)
    (removeRel : stateRelHOL jump bounds pointer
      (Tgt anything cr c {source with clock := oldClock} 0 regs)
      (StackNames.makeInit f code oracle renamed))
    (labRel : StackToLab.Proofs.StateRel.stateRel renamed lab)
    (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    Pre cr c {source with clock := newClock} regs ∧
    stateRelHOL jump bounds pointer (Tgt anything cr c {source with clock := newClock} 0 regs)
      (StackNames.makeInit f code oracle {renamed with clock := newClock}) ∧
    StackToLab.Proofs.StateRel.stateRel {renamed with clock := newClock} {lab with clock := newClock} ∧
    LabToTarget.oracleTie mc machine {lab with clock := newClock} ∧
    LabToTarget.stateRel (mc,labCode,labs,pc) {lab with clock := newClock} asm machine := by
  refine ⟨?_,?_,stackLabStateRel_setClocks renamed lab newClock labRel,?_,?_⟩
  · exact pre_setClock cr c {source with clock := oldClock} regs newClock pre
  · simpa only [Tgt, Nat.add_zero, StackNames.makeInit] using
      removeStateRel_setClocks jump bounds pointer
        (Tgt anything cr c {source with clock := oldClock} 0 regs)
        (StackNames.makeInit f code oracle renamed) newClock removeRel
  · exact LabToTarget.oracleTie_clock mc machine lab newClock tie
  · exact (LabToTarget.stateRel_clock (mc,labCode,labs,pc) lab asm machine newClock).mpr machineRel

end SteppedFlapjack.StackAllocSteps
