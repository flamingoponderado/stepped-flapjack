import SteppedFlapjack.CrepToLoopSteps.TwoEntryExecutable
import SteppedFlapjack.Concrete.BranchingLoop
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps

def branchingCrepBody : CrepProgHOL 64 :=
  .ite (.cmp .lower (.const 0) (.const 1)) (.return [.const 7]) (.return [.const 9])

private theorem branching_scalar : ScalarProgram branchingCrepBody := by
  exact .ite (.cmp .lower (.direct (.const _)) (.direct (.const _)))
    (.ret (.direct (.const _))) (.ret (.direct (.const _)))

private theorem countdown_scalar (x : BitVec 64) : ScalarProgram (countdownCrepBody x) := by
  exact .dec _ (.direct (.const _)) (.seq .skip (.seq
    (.while (.direct (.var _)) (.dec _ (.op .sub (.direct (.var _)) (.direct (.const _)))
      (.seq (.assign _ (.direct (.var _))) .skip))) (.ret (.direct (.const _)))))

private theorem naturalCountdown_scalar (x : BitVec 64) : ScalarProgram (naturalCountdownCrepBody x) := by
  exact .dec _ (.direct (.const _)) (.seq
    (.while (.direct (.var _)) (.dec _ (.op .sub (.direct (.var _)) (.direct (.const _)))
      (.seq (.assign _ (.direct (.var _))) .skip))) (.ret (.direct (.const _))))

private theorem branchingLoop_scalar : ScalarProgram branchingLoopCrepBody := by
  exact .dec _ (.direct (.const _)) (.seq
    (.while (.direct (.var _)) (.ite (.cmp .equal (.direct (.var _)) (.direct (.const _)))
      (.seq (.assign _ (.direct (.const _))) .skip) (.seq (.assign _ (.direct (.const _))) .skip)))
    (.ret (.direct (.const _))))

/-- Kernel-computable optimized code for the comparison witness. -/
theorem branching_loop_code (arch : AsmArchitecture) :
    compileProgHOLExact arch (crepPrograms branchingHOL) =
      twoLoopPrograms arch (ofString "main") (entryName branchingHOL) branchingCrepBody := by
  rw [branching_crep_code]
  exact (twoLoopPrograms_eq arch _ _ branchingCrepBody branching_scalar).symm

/-- Kernel-computable optimized code for the prefixed countdown witness. -/
theorem countdown_loop_code (arch : AsmArchitecture) (n : Nat) :
    compileProgHOLExact arch (crepPrograms (countdownHOL n)) =
      twoLoopPrograms arch (ofString "main") (entryName (countdownHOL n))
        (countdownCrepBody (BitVec.ofNat 64 n)) := by
  rw [countdown_crep_code]
  exact (twoLoopPrograms_eq arch _ _ _ (countdown_scalar _)).symm

/-- Kernel-computable optimized code for the natural countdown witness. -/
theorem naturalCountdown_loop_code (arch : AsmArchitecture) (n : Nat) :
    compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) =
      twoLoopPrograms arch (ofString "main") (entryName (naturalCountdownHOL n))
        (naturalCountdownCrepBody (BitVec.ofNat 64 n)) := by
  rw [natural_countdown_crep_code]
  exact (twoLoopPrograms_eq arch _ _ _ (naturalCountdown_scalar _)).symm

/-- Kernel-computable optimized code for the conditional-loop witness. -/
theorem branchingLoop_loop_code (arch : AsmArchitecture) :
    compileProgHOLExact arch (crepPrograms (progToHOL branchingLoop)) =
      twoLoopPrograms arch (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody := by
  rw [branchingLoop_crep_code]
  exact (twoLoopPrograms_eq arch _ _ _ branchingLoop_scalar).symm
/-- Build the Loop entry state from a phase-one Crep state and its actual code. -/
noncomputable def loopStateFrom {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) (body : ProgHOL 64) : LoopSemStateFiniteExact 64 σ :=
  PanToCrepSteps.concreteDeclLoopState arch (crepStateFrom source body) (crepPrograms body)

/-- The constructed Loop entry has the required state, memory, and global relations. -/
theorem loopStateFrom_relations {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) (body : ProgHOL 64) :
    crepToLoopStateRelExact (crepStateFrom source body) (loopStateFrom arch source body) ∧
    crepToLoopMemRelHOLExact (crepStateFrom source body).memory (loopStateFrom arch source body).memory
      (crepStateFrom source body).memaddrs ∧
    crepToLoopGlobalsRelHOLExact (crepStateFrom source body).globals (loopStateFrom arch source body).globals := by
  exact PanToCrepSteps.concreteDecl_crepLoop_relations arch (crepStateFrom source body) (crepPrograms body) rfl

end SteppedFlapjack.Concrete
