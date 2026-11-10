import SteppedFlapjack.CrepToLoopSteps.TwoEntryExecutable
import SteppedFlapjack.Concrete.BranchingLoop
import SteppedFlapjack.Concrete.CrepBranch
import SteppedFlapjack.Concrete.FrontendState
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps

theorem supported_compiled_scalar (program : Prog (RiscV.Word 64)) (supported : Supported program) (target : CrepProgHOL 64)
    (code : crepPrograms (progToHOL program) = twoPrograms (ofString "main") (entryName (progToHOL program)) target) :
    ScalarProgram target := by
  let body := progToHOL program
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  have lookup := (supported_callee_relations program supported).1
  have actual := generated_callee_lookup body target code
  have eq : compileProgExactHOLW callee body = target := by
    change (crepState body).code.lookup (entryName body) = some ([],compileProgExactHOLW callee body) at lookup
    rw [actual] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  rw [← eq]
  exact frontend_scalar_program (supported_frontend_shape supported callee)
theorem branching_scalar : ScalarProgram branchCrepBody := by
  apply supported_compiled_scalar branching branching_supported
  simpa [branching_hol_eq,twoPrograms,branchCrepBody] using branching_crep_code

theorem naturalCountdown_scalar (n : Nat) : ScalarProgram (naturalCountdownCrepBody (BitVec.ofNat 64 n)) := by
  apply supported_compiled_scalar (naturalCountdown n) (naturalCountdown_supported n)
  simpa [naturalCountdownHOL,twoPrograms] using natural_countdown_crep_code n

theorem branchingLoop_scalar : ScalarProgram branchingLoopCrepBody := by
  apply supported_compiled_scalar branchingLoop branchingLoop_supported
  simpa [twoPrograms] using branchingLoop_crep_code

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

end SteppedFlapjack.Concrete
