import Flapjack.Compiler.Backend.LabProps.DomainAlignmentSdmEvaluate
import Flapjack.Compiler.Backend.LabProps.DomainAlignment
import Flapjack.Compiler.Backend.LabToTarget.InstMem
import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Pancake.Proofs.PanToTarget

namespace SteppedFlapjack.LabToTargetSteps

private theorem good64 : goodDimindex 64 := Or.inr rfl

/-- Byte closure of a word-aligned domain: the byte-addressed domain the
machine initializer needs (`goodInitState` byte-closedness). -/
noncomputable def byteClosure (P : BitVec 64 → Bool) : BitVec 64 → Bool := fun a => P (holByteAlign a)

private theorem align_aligned (a : BitVec 64) : holByteAligned (holByteAlign a) = true := by
  rw [holByteAligned_iff_mod good64, holByteAlign_toNat good64]
  simp

private theorem align_idem (a : BitVec 64) : holByteAlign (holByteAlign a) = holByteAlign a :=
  holByteAlign_of_aligned good64 _ ((holByteAligned_iff_mod good64 _).1 (align_aligned a))

/-- `goodInitState`'s closure clause for the byte closure. -/
theorem byteClosure_closed (P : BitVec 64 → Bool) (a : BitVec 64) :
    byteClosure P (holByteAlign a) = true → byteClosure P a = true := by
  unfold byteClosure; rw [align_idem]; exact id

/-- Aligning the byte closure of an aligned domain gives the domain back. -/
theorem byteClosure_aligned (P : BitVec 64 → Bool) (hP : ∀ a, P a = true → holByteAligned a = true) :
    (fun a => byteClosure P a && holByteAligned a) = P := by
  funext a
  unfold byteClosure
  cases h : holByteAligned a
  · cases hp : P a
    · simp
    · exact absurd (hP a hp) (by simp [h])
  · rw [holByteAlign_of_aligned good64 a ((holByteAligned_iff_mod good64 a).1 h)]
    simp

/-- The P5 fixture Lab (`makeInit` with aligned word domains D, S) is the
double alignment of the machine-shaped Lab (`makeInit` with byte closures). -/
theorem makeInit_byteClosure {C S Q F : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState F) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (D Sh : BitVec 64 → Bool)
    (hD : ∀ a, D a = true → holByteAligned a = true) (hS : ∀ a, Sh a = true → holByteAligned a = true)
    (ms : S) (code : LabSem.LabProgHOL 64)
    (comp : C → LabSem.LabProgHOL 64 → Option (List (BitVec 8) × C))
    (cbpos : BitVec 64) (cbspace : Nat) (co : Nat → C × LabSem.LabProgHOL 64) :
    alignSdm (alignDm (makeInit mc ffi t m (byteClosure D) (byteClosure Sh) ms code comp cbpos cbspace co)) =
      makeInit mc ffi t m D Sh ms code comp cbpos cbspace co := by
  simp only [alignSdm, alignDm, makeInit, byteClosure_aligned D hD, byteClosure_aligned Sh hS]

/-- Transfer a halting run through shared-domain alignment (any clock). -/
theorem halt_of_alignSdm {C F : Type} (s : LabSem.State 64 C F) (clock : Nat) (o : HolOutcome)
    (post : LabSem.State 64 C F)
    (run : LabSem.evaluate {alignSdm s with clock := clock} = (.halt o, post)) :
    ∃ next, LabSem.evaluate {s with clock := clock} = (.halt o, next) ∧ next.ffi = post.ffi := by
  rw [← alignSdmWithClock, evaluateAlignSDM good64] at run
  rcases h : LabSem.evaluate {s with clock := clock} with ⟨r, next⟩
  rw [h] at run
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨next, rfl, rfl⟩

end SteppedFlapjack.LabToTargetSteps
