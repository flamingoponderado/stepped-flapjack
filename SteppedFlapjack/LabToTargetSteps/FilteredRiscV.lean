import SteppedFlapjack.LabToTargetSteps.LabRiscVComposition
import Flapjack.Compiler.Backend.LabFilter.Proofs.FilterCorrect
import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClock

/-! Bounded transfer from the unfiltered Lab program to its compiled RISC-V code. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Resetting both clocks preserves the filter simulation relation. -/
theorem filterRel_withClock {width : Nat} [NeZero width] {C F : Type}
    (filtered original : LabSem.State width C F) (clock : Nat)
    (rel : LabFilter.Proofs.stateRel filtered original) :
    LabFilter.Proofs.stateRel {filtered with clock := clock} {original with clock := clock} := by
  rcases rel with ⟨⟨comp,hfiltered,hcomp⟩,hfailed⟩
  subst filtered
  exact ⟨⟨comp,rfl,hcomp⟩,hfailed⟩

/-- Removing skips preserves any terminating Lab evaluation at the same clock,
including its final FFI state. -/
theorem filteredLab_halt_sameClock {width : Nat} [NeZero width] {C F : Type}
    (filtered original : LabSem.State width C F) (clock : Nat)
    (outcome : HolOutcome) (post : LabSem.State width C F)
    (rel : LabFilter.Proofs.stateRel filtered original)
    (run : evaluate {original with clock := clock} = (.halt outcome,post)) :
    ∃ filteredPost, evaluate {filtered with clock := clock} = (.halt outcome,filteredPost) ∧
      filteredPost.ffi = post.ffi := by
  have relClock : LabFilter.Proofs.stateRel {filtered with clock := clock} {original with clock := clock} := by
    rcases rel with ⟨⟨compile, hfiltered, hcompile⟩, hfailed⟩
    subst filtered
    exact ⟨⟨compile,rfl,hcompile⟩,hfailed⟩
  let result := evaluate {filtered with clock := clock}
  obtain ⟨extra,final,heval,hffi⟩ := LabFilter.Proofs.filterCorrect
    {filtered with clock := clock} {original with clock := clock} result.1 result.2
    ⟨rfl,relClock,relClock.2⟩
  have hextend := LabProps.evaluateAddClock {original with clock := clock}
    (.halt outcome) post extra ⟨run,by simp⟩
  have heval' : evaluate {original with clock := clock+extra} = (result.1,final) := by
    simpa only using heval
  have hextend' : evaluate {original with clock := clock+extra} = (.halt outcome,{post with clock := post.clock+extra}) := by
    simpa only using hextend
  rw [hextend'] at heval'
  have heq := Prod.mk.inj heval'
  refine ⟨result.2,?_,?_⟩
  · exact Prod.ext heq.1.symm rfl
  · simpa only [← heq.2] using hffi

/-- The two actual Lab initializers satisfy the skip-filter simulation relation. -/
theorem makeInit_filterRel {width : Nat} [NeZero width] {C S Q F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (asm : AsmState width)
    (memory : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (machine : S) (code : LabProgHOL width)
    (comp : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (oracle : Nat → C × LabProgHOL width) :
    LabFilter.Proofs.stateRel
      (makeInit mc ffi asm memory dm sdm machine (LabFilter.filterSkip code) comp cbpos cbspace
        (fun n => ((oracle n).1,LabFilter.filterSkip (oracle n).2)))
      (makeInit mc ffi asm memory dm sdm machine code
        (fun c p => comp c (LabFilter.filterSkip p)) cbpos cbspace oracle) := by
  refine ⟨⟨comp,?_,rfl⟩,rfl⟩
  simp only [makeInit]
  rw [LabFilter.Proofs.adjustPc.eq_def]
  simp

/-- A bounded run of the unfiltered Lab program bounds the machine execution
of its skip-filtered compilation by the same Lab clock. -/
theorem unfilteredLabToRiscVWithin {F : Type}
    (p : BitVec 64) (filtered original originalPost : LabSem.State 64 Config F)
    (outcome : HolOutcome) (clock bound : Nat)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (code : LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget)
    (filterRel : LabFilter.Proofs.stateRel filtered original)
    (tie : oracleTie mc machine filtered) (rel : stateRel (mc,code,labs,p) filtered asm machine)
    (run : evaluate {original with clock := clock} = (.halt outcome,originalPost)) (hbound : clock ≤ bound) :
    ∃ ticks finalMachine, ticks ≤ labTickBound 4 code filtered.codeBuffer * bound ∧
      evaluateTargetHOL mc original.ffi ticks machine = (.halt outcome,finalMachine,originalPost.ffi) := by
  obtain ⟨filteredPost,filteredRun,postFfi⟩ :=
    filteredLab_halt_sameClock filtered original clock outcome originalPost filterRel run
  have initialFfi : filtered.ffi = original.ffi := by
    obtain ⟨⟨_,h,_⟩,_⟩ := filterRel
    rw [h]
  obtain ⟨ticks,finalMachine,hticks,hrun⟩ :=
    labToRiscVWithin p filtered filteredPost outcome clock bound mc code labs asm machine
      hmc tie rel filteredRun hbound
  exact ⟨ticks,finalMachine,hticks,by simpa only [initialFfi,postFfi] using hrun⟩

/-- The original and filtered initializers need no separate simulation
hypothesis when transferring a bounded Lab run to the RISC-V machine. -/
theorem makeInit_unfilteredToRiscVWithin {F : Type}
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ffi : HolFfiState F)
    (asm : AsmState 64) (memory : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (machine : RiscV.L3.riscv_state) (program : LabProgHOL 64) (cbpos : BitVec 64) (cbspace : Nat)
    (oracle : Nat → Config × LabProgHOL 64) (p : BitVec 64) (code : LabProgHOL 64) (labs : Spt (Spt Nat))
    (outcome : HolOutcome) (clock bound : Nat) (post : LabSem.State 64 Config F)
    (hmc : mc.target = riscvTarget)
    (tie : oracleTie mc machine (makeInit mc ffi asm memory dm sdm machine (LabFilter.filterSkip program)
      (compileLab mc.target.config) cbpos cbspace (fun n => ((oracle n).1,LabFilter.filterSkip (oracle n).2))))
    (rel : stateRel (mc,code,labs,p) (makeInit mc ffi asm memory dm sdm machine (LabFilter.filterSkip program)
      (compileLab mc.target.config) cbpos cbspace (fun n => ((oracle n).1,LabFilter.filterSkip (oracle n).2))) asm machine)
    (run : evaluate {makeInit mc ffi asm memory dm sdm machine program (LabToTarget.compile mc.target.config)
      cbpos cbspace oracle with clock := clock} = (.halt outcome,post)) (hbound : clock ≤ bound) :
    ∃ ticks finalMachine, ticks ≤ labTickBound 4 code (makeInit mc ffi asm memory dm sdm machine
      (LabFilter.filterSkip program) (compileLab mc.target.config) cbpos cbspace
      (fun n => ((oracle n).1,LabFilter.filterSkip (oracle n).2))).codeBuffer * bound ∧
      evaluateTargetHOL mc ffi ticks machine = (.halt outcome,finalMachine,post.ffi) := by
  have hfilter := makeInit_filterRel mc ffi asm memory dm sdm machine program
    (compileLab mc.target.config) cbpos cbspace oracle
  have hrun := unfilteredLabToRiscVWithin p _ _ post outcome clock bound mc code labs asm machine
    hmc hfilter tie rel run hbound
  simpa only [makeInit] using hrun

end SteppedFlapjack.LabToTargetSteps
