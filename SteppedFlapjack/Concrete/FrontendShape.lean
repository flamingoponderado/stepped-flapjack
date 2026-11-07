import SteppedFlapjack.Concrete.SourceRuns
import SteppedFlapjack.PanToCrepSteps.DeclShape

/-! Connect source scalar syntax to the frontend's singleton-result expressions. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

/-- Each in-scope source variable has a scalar register in the frontend context. -/
def ScopeRelation (scope : List VarName) (ctxt : PanToCrepContextExact 64) : Prop :=
  ∀ name ∈ scope, ∃ reg, ctxt.vars.lookup (ofString name) = some (.one,[reg])

/-- A scalar expression the Pancake frontend compiles to one Crep expression.
The direct subset also supports the existing no-auxiliary-code Loop proofs;
comparisons may generate additional Loop code in a later pass. -/
inductive FrontendScalar (ctxt : PanToCrepContextExact 64) : ExpHOL 64 → Prop
  | direct {e} : ScalarExpression ctxt e → FrontendScalar ctxt e
  | op (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.op operator [a,b])
  | cmp (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.cmp operator a b)
  | shift (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.shift operator a b)

/-- Every frontend scalar produces exactly one Crep expression. -/
theorem frontendScalar_compile {ctxt : PanToCrepContextExact 64} {e : ExpHOL 64}
    (shape : FrontendScalar ctxt e) : ∃ value, compileExpExactHOLW ctxt e = ([value],.one) := by
  induction shape with
  | direct h => obtain ⟨v,compiled,_⟩ := scalar_compile h; exact ⟨v,compiled⟩
  | op op ha hb iha ihb =>
    obtain ⟨a,ca⟩ := iha
    obtain ⟨b,cb⟩ := ihb
    exact ⟨.op op [a,b],by simp [compileExpExactHOLW,compileExpExactHOLWList,ca,cb,cexpHeads]⟩
  | cmp op ha hb iha ihb =>
    obtain ⟨a,ca⟩ := iha
    obtain ⟨b,cb⟩ := ihb
    exact ⟨.cmp op a b,by simp [compileExpExactHOLW,ca,cb]⟩
  | shift op ha hb iha ihb =>
    obtain ⟨a,ca⟩ := iha
    obtain ⟨b,cb⟩ := ihb
    exact ⟨.shift op a b,by simp [compileExpExactHOLW,ca,cb]⟩

/-- Generalized scalar declarations compile with the actual extended context,
including when the initializer contains comparisons. -/
theorem frontendDecl_compile (ctxt : PanToCrepContextExact 64) (name : MlString)
    (initializer : ExpHOL 64) (body : ProgHOL 64) (shape : FrontendScalar ctxt initializer) :
    ∃ value, compileProgExactHOLW ctxt (.dec name .one initializer body) =
      .dec (ctxt.vmax+1) value (compileProgExactHOLW (scalarDeclContext ctxt name) body) := by
  obtain ⟨value,compiled⟩ := frontendScalar_compile shape
  refine ⟨value,?_⟩
  simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext]

/-- Generalized scalar conditions are passed to the generated Crep conditional. -/
theorem frontendIf_compile (ctxt : PanToCrepContextExact 64)
    (condition : ExpHOL 64) (yes no : ProgHOL 64) (shape : FrontendScalar ctxt condition) :
    ∃ value, compileProgExactHOLW ctxt (.ite condition yes no) =
      .ite value (compileProgExactHOLW ctxt yes) (compileProgExactHOLW ctxt no) := by
  obtain ⟨value,compiled⟩ := frontendScalar_compile shape
  exact ⟨value,by simp [compileProgExactHOLW,compileIfExactHOLW,compiled]⟩

/-- Generalized scalar conditions are passed to the generated Crep loop. -/
theorem frontendWhile_compile (ctxt : PanToCrepContextExact 64)
    (condition : ExpHOL 64) (body : ProgHOL 64) (shape : FrontendScalar ctxt condition) :
    ∃ value, compileProgExactHOLW ctxt (.while condition body) =
      .while value (compileProgExactHOLW ctxt body) := by
  obtain ⟨value,compiled⟩ := frontendScalar_compile shape
  exact ⟨value,by simp [compileProgExactHOLW,compileWhileExactHOLW,compiled]⟩

/-- Source scalar syntax has the generalized frontend shape when its locals
are represented in the compiler context. -/
theorem scalar_frontend_shape {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    (relation : ScopeRelation scope ctxt) {e : Exp (RiscV.Word 64)} (scalar : Scalar scope e) :
    FrontendScalar ctxt (expToHOL e) := by
  induction scalar with
  | const v => simpa [expToHOL] using (FrontendScalar.direct (ctxt := ctxt) (.const v))
  | «local» name member =>
    obtain ⟨reg,found⟩ := relation name member
    simpa [expToHOL] using (FrontendScalar.direct (.local (ofString name) reg found))
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

/-- The generalized Pancake frontend fragment, tracking the compiler context
through declarations and allowing nested control flow and comparisons. -/
inductive FrontendProgram : PanToCrepContextExact 64 → ProgHOL 64 → Prop
  | skip {ctxt} : FrontendProgram ctxt .skip
  | assign {ctxt name e} (reg : Nat) : ctxt.vars.lookup name = some (.one,[reg]) →
      FrontendScalar ctxt e → FrontendProgram ctxt (.assign .local name e)
  | decl {ctxt name e body} : FrontendScalar ctxt e →
      FrontendProgram (scalarDeclContext ctxt name) body → FrontendProgram ctxt (.dec name .one e body)
  | seq {ctxt a b} : FrontendProgram ctxt a → FrontendProgram ctxt b → FrontendProgram ctxt (.seq a b)
  | ite {ctxt e a b} : FrontendScalar ctxt e → FrontendProgram ctxt a → FrontendProgram ctxt b →
      FrontendProgram ctxt (.ite e a b)
  | while {ctxt e body} : FrontendScalar ctxt e → FrontendProgram ctxt body → FrontendProgram ctxt (.while e body)
  | ret {ctxt e} : FrontendScalar ctxt e → FrontendProgram ctxt (.return e)

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
  · exact .cmp .less (.direct (.const 0)) (.direct (.const 1))
  · simp [compileExpExactHOLW]

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
