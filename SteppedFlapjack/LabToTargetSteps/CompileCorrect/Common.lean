import Flapjack.Compiler.Backend.LabToTarget.StateTransport
import Flapjack.Compiler.Backend.LabSem.Evaluate
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect
import SteppedFlapjack.LabToTargetSteps.Defs
import Flapjack.Compiler.Backend.Semantics.TargetSem.Evaluate

/-! Adapted copy of `Flapjack/Compiler/Backend/LabToTarget/CompileCorrect/Common.lean`
(stepped-flapjack#2, phase B). `CompileCorrectFor` becomes
`CompileCorrectWithinFor S Q unit steps`: the encoder hypothesis is
`encoderCorrectWithin mc.target steps` together with
`StepsFit unit steps mc.target`, and the conclusion adds
`k ≤ (labTickBound unit code2 s1.codeBuffer - 1) * s1.clock`, so the target
run takes at most `labTickBound unit code2 s1.codeBuffer` ticks per source
clock tick. `compileCorrect_step` takes the bound on the step's tick count `l`
and on the tick bound of the next source state. Otherwise the statements and
proofs follow the original. -/

/-! Shared statement shape of the original `compile_correct`
(lab_to_targetProofScript.sml:7528-7558) and the composition step used by
every case: one simulated target step followed by the induction hypothesis
for the next source state. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.Asm

/-- The conclusion of the original `compile_correct` for one source state:
every machine configuration, result, final source state, target code, label
map, target state, machine state and code base related to it by the full
`state_rel` and `oracle_tie`, with a non-`Error` source result and an encoder
correct within `steps` ticks per instruction, where `StepsFit unit steps`,
has a target run with the same result and final FFI state, taking at most
`labTickBound unit code2 s1.codeBuffer - 1` ticks more than the source clock
per source clock tick. The original existential also binds an unused `t2`,
which is omitted. The machine and projection carriers are parameters, as the
HOL type variables `'state` and `'b` are fixed by the theorem. -/
def CompileCorrectWithinFor {width : Nat} [NeZero width] (S Q : Type) {F : Type}
    (unit : Nat) (steps : HolAsm width → Nat) (s1 : LabSem.State width Config F) : Prop :=
  ∀ (res : MachineResult) (mc : MachineConfig width S Q) (s2 : LabSem.State width Config F)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (p : BitVec width),
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrectWithin mc.target steps ∧ StepsFit unit steps mc.target ∧
      stateRel (mc, code2, labs, p) s1 t1 ms1 →
    ∃ k ms2, k ≤ (labTickBound unit code2 s1.codeBuffer - 1) * s1.clock ∧
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi)

/-- One simulated target step followed by the induction hypothesis for the
next source state; Flapjack infrastructure for the common tail of the
original case proofs (`oracle_tie_step` and the final clock arithmetic). -/
theorem compileCorrect_step {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 s1' s2 : LabSem.State width Config F} {t1' : AsmState width}
    {ms1 ms2 : S} {res : MachineResult} {l : Nat} {unit : Nat} {steps : HolAsm width → Nat}
    (ht : oracleTie mc ms1 s1) (hec : encoderCorrectWithin mc.target steps)
    (hfit : StepsFit unit steps mc.target) (hclock : s1.clock ≠ 0)
    (hl : ∀ k, evaluateTargetHOL mc s1.ffi (k + l) ms1 =
        evaluateTargetHOL (shiftInterfer l mc) s1.ffi k ms2 ∧
      findNextInterference mc s1.ffi (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) s1.ffi k ms2)
    (hl0 : l ≠ 0) (hlb : l ≤ labTickBound unit code2 s1.codeBuffer - 1)
    (hcb : labTickBound unit code2 s1'.codeBuffer ≤ labTickBound unit code2 s1.codeBuffer)
    (hs' : s1'.clock = s1.clock - 1 ∧ s1'.ffi = s1.ffi ∧ s1'.ioRegs = s1.ioRegs ∧
      s1'.ioFpRegs = s1.ioFpRegs ∧ s1'.ccRegs = s1.ccRegs ∧ s1'.ccFpRegs = s1.ccFpRegs)
    (hrel' : stateRel (shiftInterfer l mc, code2, labs, p) s1' t1' ms2)
    (hev : evaluate s1' = (res, s2)) (hres : res ≠ .error)
    (ih : CompileCorrectWithinFor S Q unit steps s1') :
    ∃ k ms3, k ≤ (labTickBound unit code2 s1.codeBuffer - 1) * s1.clock ∧
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) := by
  obtain ⟨hc, hffi, hio, hiofp, hcc, hccfp⟩ := hs'
  have ht' : oracleTie (shiftInterfer l mc) ms2 s1' :=
    oracleTie_step mc ms1 ms2 s1 s1' l ⟨ht, fun k => (hl k).2, hio, hiofp, hcc, hccfp, hffi⟩
  obtain ⟨k', ms3, hkb, hk⟩ := ih res (shiftInterfer l mc) s2 code2 labs t1' ms2 p
    ⟨ht', hev, hres, hec, hfit, hrel'⟩
  refine ⟨k' + l - 1, ms3, ?_, ?_⟩
  · rw [hc] at hkb
    exact tick_step_bound hclock (tick_bound_mono hcb hkb) (by omega)
  rw [show s1.clock + (k' + l - 1) = (s1'.clock + k') + l by omega, (hl _).1, ← hffi]
  exact hk

end SteppedFlapjack.LabToTargetSteps
