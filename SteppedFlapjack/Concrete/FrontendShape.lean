import SteppedFlapjack.Concrete.SourceRuns
import SteppedFlapjack.PanToCrepSteps.FrontendProgram

/-! Connect source scalar syntax to the frontend's singleton-result expressions. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

/-- Each in-scope source variable has a scalar register in the frontend context. -/
def ScopeRelation (scope : List VarName) (ctxt : PanToCrepContextExact 64) : Prop :=
  ∀ name ∈ scope, ∃ reg, ctxt.vars.lookup (ofString name) = some (.one,[reg])

/-- Source scalar syntax has the generalized frontend shape when its locals
are represented in the compiler context. -/
theorem scalar_frontend_shape {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    (relation : ScopeRelation scope ctxt) {e : Exp (RiscV.Word 64)} (scalar : Scalar scope e) :
    FrontendScalar ctxt (expToHOL e) := by
  induction scalar with
  | const v => simpa [expToHOL] using (FrontendScalar.const (ctxt := ctxt) v)
  | «local» name member =>
    obtain ⟨reg,found⟩ := relation name member
    simpa [expToHOL] using (FrontendScalar.local (ofString name) reg found)
  | op op a b iha ihb => simpa [expToHOL] using (FrontendScalar.op op iha ihb)
  | cmp op a b iha ihb => simpa [expToHOL] using (FrontendScalar.cmp op iha ihb)
  | shift op a b iha ihb => simpa [expToHOL] using (FrontendScalar.shift op iha ihb)

/-- A new declaration extends the register context, including shadowing. -/
theorem ScopeRelation.declare {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    (relation : ScopeRelation scope ctxt) (name : VarName) :
    ScopeRelation (name :: scope) (scalarDeclContext ctxt (ofString name)) := by
  intro item member
  simp only [List.mem_cons] at member
  rcases member with eq | member
  · subst item
    exact ⟨_,scalarDeclContext_local ctxt (ofString name)⟩
  · by_cases same : ofString item = ofString name
    · exact ⟨_,by rw [same]; exact scalarDeclContext_local ctxt (ofString name)⟩
    · obtain ⟨reg,found⟩ := relation item member
      refine ⟨reg,?_⟩
      simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same,Ne.symm same] using found

/-- All supported source programs have the generalized frontend shape. -/
theorem supportedIn_frontend_shape {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ∀ ctxt, ScopeRelation scope ctxt →
      FrontendProgram ctxt (progToHOL program) := by
  induction supported with
  | skip => intro ctxt relation; simpa [progToHOL] using (FrontendProgram.skip (ctxt := ctxt))
  | assign name member e =>
    intro ctxt relation
    obtain ⟨reg,found⟩ := relation name member
    simpa [progToHOL] using (FrontendProgram.assign reg found (scalar_frontend_shape relation e))
  | decl name e body ih =>
    intro ctxt relation
    simpa [progToHOL,shapeToHOL] using
      (FrontendProgram.decl (scalar_frontend_shape relation e) (ih _ (relation.declare name)))
  | seq a b iha ihb =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.seq (iha ctxt relation) (ihb ctxt relation))
  | ite e a b iha ihb =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.ite (scalar_frontend_shape relation e) (iha ctxt relation) (ihb ctxt relation))
  | «while» e body ih =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.while (scalar_frontend_shape relation e) (ih ctxt relation))
  | ret e =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.ret (scalar_frontend_shape relation e))

theorem supported_frontend_shape {program : Prog (RiscV.Word 64)} (supported : Supported program)
    (ctxt : PanToCrepContextExact 64) : FrontendProgram ctxt (progToHOL program) :=
  supportedIn_frontend_shape supported ctxt (by intro name member; simp at member)

/-- A comparison is accepted in an actual conditional and compiles to a
single Crep comparison expression. -/
theorem comparison_frontend_example (ctxt : PanToCrepContextExact 64) :
    FrontendScalar ctxt (.cmp .less (.const 0) (.const 1)) ∧
    compileExpExactHOLW ctxt (.cmp .less (.const 0) (.const 1) : ExpHOL 64) =
      ([.cmp .less (.const 0) (.const 1)],.one) := by
  constructor
  · exact .cmp .less (.const 0) (.const 1)
  · simp [compileExpExactHOLW]

/-- Global lowering leaves the supported scalar expressions unchanged. -/
theorem scalar_globals_fixed {scope : List VarName} {e : Exp (RiscV.Word 64)}
    (scalar : Scalar scope e) (globals : PanGlobalsContextExact 64) :
    compileExpExactHOL globals (expToHOL e) = expToHOL e := by
  induction scalar <;> simp_all [expToHOL,compileExpExactHOL,compileExpExactHOLList]

/-- Global lowering leaves every supported source body unchanged. -/
theorem supportedIn_globals_fixed {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (globals : PanGlobalsContextExact 64) :
    compileProgExactHOL globals (progToHOL program) = progToHOL program := by
  induction supported <;> simp_all [progToHOL,compileProgExactHOL,shapeToHOL] <;>
    aesop (add safe scalar_globals_fixed)

theorem supported_globals_fixed {program : Prog (RiscV.Word 64)}
    (supported : Supported program) (globals : PanGlobalsContextExact 64) :
    compileProgExactHOL globals (progToHOL program) = progToHOL program :=
  supportedIn_globals_fixed supported globals

/-- The phase-zero witnesses instantiate the generalized frontend shape. -/
theorem countdown_frontend_shape (n : Nat) (ctxt : PanToCrepContextExact 64) :
    FrontendProgram ctxt (countdownHOL n) := by
  rw [countdown_hol_eq]
  exact supported_frontend_shape (countdown_supported n) ctxt

theorem branching_frontend_shape (ctxt : PanToCrepContextExact 64) :
    FrontendProgram ctxt branchingHOL := by
  rw [branching_hol_eq]
  exact supported_frontend_shape branching_supported ctxt

end SteppedFlapjack.Concrete
