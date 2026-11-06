import SteppedFlapjack.PanToCrepSteps.Shape

/-! Exact compilation of a scalar local declaration. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.CrepToLoopSteps

/-- The body of a scalar declaration is compiled under the fresh local binding
allocated by the actual Pancake-to-Crep compiler. -/
def scalarDeclContext {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) : PanToCrepContextExact width :=
  { ctxt with vars := ctxt.vars.update (name,(.one,[ctxt.vmax+1])), vmax := ctxt.vmax+1 }

/-- The newly declared scalar is available to the body as a singleton local. -/
theorem scalarDeclContext_local {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) :
    (scalarDeclContext ctxt name).vars.lookup name = some (.one,[ctxt.vmax+1]) := by
  simp [scalarDeclContext,FUPDATE]

/-- A scalar declaration compiles to one Crep declaration around the actual
body compilation, with a direct initializer expression. -/
theorem scalarDecl_compile {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (initializer : ExpHOL width)
    (body : ProgHOL width) (shape : ScalarExpression ctxt initializer) :
    ∃ value, DirectExpression value ∧
      compileProgExactHOLW ctxt (.dec name .one initializer body) =
        .dec (ctxt.vmax+1) value (compileProgExactHOLW (scalarDeclContext ctxt name) body) := by
  obtain ⟨value,compiled,direct⟩ := scalar_compile shape
  refine ⟨value,direct,?_⟩
  simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext]

end SteppedFlapjack.PanToCrepSteps
