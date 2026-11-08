import SteppedFlapjack.CrepToLoopSteps.TwoEntryExecutable
import SteppedFlapjack.Concrete.BranchingLoop
import SteppedFlapjack.Concrete.CrepBranch
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps

private theorem branching_scalar : ScalarProgram branchCrepBody := by
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
      twoLoopPrograms arch (ofString "main") (entryName branchingHOL) branchCrepBody := by
  rw [branching_crep_code]
  exact (twoLoopPrograms_eq arch _ _ branchCrepBody branching_scalar).symm

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

def witnessLoopContext (arch : AsmArchitecture) (body : ProgHOL 64) : CrepToLoopContextExact :=
  mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (crepPrograms body)) 0

/-- Actual generated code tables satisfy compiler code and empty-live relations. -/
theorem loopStateFrom_code_locals {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) (body : ProgHOL 64) (calleeBody : CrepProgHOL 64)
    (shape : ScalarProgram calleeBody)
    (code : crepPrograms body = twoPrograms (ofString "main") (entryName body) calleeBody) :
    crepToLoopCodeRelExact (witnessLoopContext arch body) (crepStateFrom source body).code
        (loopStateFrom arch source body).code ∧
    crepToLoopLocalsRelExact (witnessLoopContext arch body) .ln (crepStateFrom source body).locals
        (loopStateFrom arch source body).locals := by
  have fresh : ofString "main" ≠ entryName body := Ne.symm (entryName_fresh body)
  have relation := twoPrograms_codeRel arch _ _ calleeBody fresh shape
  constructor
  · simpa [witnessLoopContext,loopStateFrom,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,
      PanToCrepSteps.concreteDeclLoopState,code] using relation
  · apply PanToCrepSteps.empty_crepLoop_locals
    simp [witnessLoopContext,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq]
/-- The comparison witness needs no separate code or locals premises. -/
theorem branching_loop_code_locals {σ : Type} (arch : AsmArchitecture) (source : PanSemStateFiniteExact 64 σ) :
    crepToLoopCodeRelExact (witnessLoopContext arch branchingHOL) (crepStateFrom source branchingHOL).code
      (loopStateFrom arch source branchingHOL).code ∧
    crepToLoopLocalsRelExact (witnessLoopContext arch branchingHOL) .ln (crepStateFrom source branchingHOL).locals
      (loopStateFrom arch source branchingHOL).locals := by
  apply loopStateFrom_code_locals arch source branchingHOL branchCrepBody branching_scalar
  simpa [twoPrograms,branchCrepBody] using branching_crep_code

/-- The countdown witness needs no separate code or locals premises. -/
theorem countdown_loop_code_locals {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) (n : Nat) :
    crepToLoopCodeRelExact (witnessLoopContext arch (countdownHOL n)) (crepStateFrom source (countdownHOL n)).code
      (loopStateFrom arch source (countdownHOL n)).code ∧
    crepToLoopLocalsRelExact (witnessLoopContext arch (countdownHOL n)) .ln (crepStateFrom source (countdownHOL n)).locals
      (loopStateFrom arch source (countdownHOL n)).locals := by
  apply loopStateFrom_code_locals arch source (countdownHOL n) _ (countdown_scalar _)
  simpa [twoPrograms] using countdown_crep_code n

/-- The unprefixed countdown witness has the same constructed relations. -/
theorem naturalCountdown_loop_code_locals {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) (n : Nat) :
    crepToLoopCodeRelExact (witnessLoopContext arch (naturalCountdownHOL n)) (crepStateFrom source (naturalCountdownHOL n)).code
      (loopStateFrom arch source (naturalCountdownHOL n)).code ∧
    crepToLoopLocalsRelExact (witnessLoopContext arch (naturalCountdownHOL n)) .ln (crepStateFrom source (naturalCountdownHOL n)).locals
      (loopStateFrom arch source (naturalCountdownHOL n)).locals := by
  apply loopStateFrom_code_locals arch source (naturalCountdownHOL n) _ (naturalCountdown_scalar _)
  simpa [twoPrograms] using natural_countdown_crep_code n

/-- The conditional-loop witness has the same constructed relations. -/
theorem branchingLoop_loop_code_locals {σ : Type} (arch : AsmArchitecture) (source : PanSemStateFiniteExact 64 σ) :
    crepToLoopCodeRelExact (witnessLoopContext arch (progToHOL branchingLoop)) (crepStateFrom source (progToHOL branchingLoop)).code
      (loopStateFrom arch source (progToHOL branchingLoop)).code ∧
    crepToLoopLocalsRelExact (witnessLoopContext arch (progToHOL branchingLoop)) .ln
      (crepStateFrom source (progToHOL branchingLoop)).locals (loopStateFrom arch source (progToHOL branchingLoop)).locals := by
  apply loopStateFrom_code_locals arch source (progToHOL branchingLoop) _ branchingLoop_scalar
  simpa [twoPrograms] using branchingLoop_crep_code

end SteppedFlapjack.Concrete
