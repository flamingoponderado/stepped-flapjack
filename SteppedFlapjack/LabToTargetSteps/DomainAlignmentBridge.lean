import SteppedFlapjack.LabToTargetSteps.FilteredRiscV
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentDmEvaluate

/-! Preserve bounded runs when the Stack-side Lab domain is word-aligned. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target

/-- A terminating run with an aligned domain implies an unaligned-domain run
at the same clock and with the same final FFI state. -/
theorem unalignLab_halt_sameClock {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (original : LabSem.State width C F) (clock : Nat)
    (outcome : HolOutcome) (post : LabSem.State width C F)
    (run : evaluate {alignDm original with clock := clock} = (.halt outcome,post)) :
    ∃ originalPost, evaluate {original with clock := clock} = (.halt outcome,originalPost) ∧
      originalPost.ffi = post.ffi := by
  have relation := evaluateAlignDM hw {original with clock := clock}
  change evaluate {alignDm original with clock := clock} = _ at relation
  cases hrun : evaluate {original with clock := clock} with
  | mk res final =>
    simp only [hrun] at relation
    rw [run] at relation
    obtain ⟨hout,hpost⟩ := Prod.mk.inj relation
    refine ⟨final,?_,?_⟩
    · rw [hout]
    · simp only [hpost,alignDm]

/-- Combine byte-domain alignment with skip filtering and the existing
Lab-to-RISC-V bound, without increasing the Lab clock. -/
theorem alignedUnfilteredLabToRiscVWithin {F : Type}
    (p : BitVec 64) (filtered original post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (clock bound : Nat)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (code : LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (filterRel : LabFilter.Proofs.stateRel filtered original)
    (tie : oracleTie mc machine filtered) (rel : stateRel (mc,code,labs,p) filtered asm machine)
    (run : evaluate {alignDm original with clock := clock} = (.halt outcome,post)) (hbound : clock ≤ bound) :
    ∃ ticks finalMachine, ticks ≤ labTickBound 4 code filtered.codeBuffer * bound ∧
      evaluateTargetHOL mc original.ffi ticks machine = (.halt outcome,finalMachine,post.ffi) := by
  obtain ⟨originalPost,originalRun,ffi⟩ := unalignLab_halt_sameClock (by simp [goodDimindex]) original clock outcome post run
  obtain ⟨ticks,finalMachine,hticks,hrun⟩ := unfilteredLabToRiscVWithin p filtered original originalPost outcome clock bound
    mc code labs asm machine hmc filterRel tie rel originalRun hbound
  exact ⟨ticks,finalMachine,hticks,by simpa only [ffi] using hrun⟩

/-- The machine Lab state is either the Stack-side state, its filtered form,
or the filtered byte-domain state corresponding to an aligned Stack domain. -/
def LabExecutionLink {F : Type} (filtered stackLab : LabSem.State 64 Config F) : Prop :=
  filtered = stackLab ∨ LabFilter.Proofs.stateRel filtered stackLab ∨
    ∃ raw, stackLab = alignDm raw ∧ LabFilter.Proofs.stateRel filtered raw

/-- Every supported relation preserves the code buffer. -/
theorem LabExecutionLink.codeBuffer {F : Type} {filtered stackLab : LabSem.State 64 Config F}
    (link : LabExecutionLink filtered stackLab) : filtered.codeBuffer = stackLab.codeBuffer := by
  rcases link with rfl | h | ⟨raw,rfl,h⟩
  · rfl
  · obtain ⟨⟨_,eq,_⟩,_⟩ := h
    rw [eq]
  · obtain ⟨⟨_,eq,_⟩,_⟩ := h
    rw [eq]
    rfl

/-- Resetting both clocks preserves either execution link. -/
theorem LabExecutionLink.withClock {F : Type} {filtered stackLab : LabSem.State 64 Config F}
    (link : LabExecutionLink filtered stackLab) (clock : Nat) :
    LabExecutionLink {filtered with clock := clock} {stackLab with clock := clock} := by
  rcases link with rfl | h | ⟨raw,rfl,h⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (filterRel_withClock _ _ clock h))
  · exact Or.inr (Or.inr ⟨{raw with clock := clock},rfl,filterRel_withClock _ _ clock h⟩)

/-- Either supported Lab execution link transfers a bounded Stack-side run to
RISC-V with the same clock and FFI observation. -/
theorem connectedLabToRiscVWithin {F : Type}
    (p : BitVec 64) (filtered stackLab post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (clock bound : Nat)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (code : LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (link : LabExecutionLink filtered stackLab)
    (tie : oracleTie mc machine filtered) (rel : stateRel (mc,code,labs,p) filtered asm machine)
    (run : evaluate {stackLab with clock := clock} = (.halt outcome,post)) (hbound : clock ≤ bound) :
    ∃ ticks finalMachine, ticks ≤ labTickBound 4 code filtered.codeBuffer * bound ∧
      evaluateTargetHOL mc stackLab.ffi ticks machine = (.halt outcome,finalMachine,post.ffi) := by
  rcases link with rfl | h | ⟨raw,rfl,h⟩
  · exact labToRiscVWithin p filtered post outcome clock bound mc code labs asm machine hmc tie rel run hbound
  · exact unfilteredLabToRiscVWithin p filtered stackLab post outcome clock bound mc code labs asm machine hmc h tie rel run hbound
  · exact alignedUnfilteredLabToRiscVWithin p filtered raw post outcome clock bound mc code labs asm machine hmc h tie rel run hbound

end SteppedFlapjack.LabToTargetSteps
