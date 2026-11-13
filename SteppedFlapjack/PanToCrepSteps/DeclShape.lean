import SteppedFlapjack.PanToCrepSteps.Shape

/-! Exact compilation of a scalar local declaration. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.CrepToLoopSteps

/-- Allocation context and compiled declaration for an arbitrary value shape. -/
def valueDeclContext {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (shape : ShapeHOL) : PanToCrepContextExact width :=
  let count := sizeOfShapeHOL shape
  let names := (List.range count).map (fun index => ctxt.vmax + index + 1)
  {ctxt with vars := ctxt.vars.update (name,(shape,names)), vmax := ctxt.vmax + count}

theorem valueDeclContext_local {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (shape : ShapeHOL) :
    let names := (List.range (sizeOfShapeHOL shape)).map (fun index => ctxt.vmax + index + 1)
    (valueDeclContext ctxt name shape).vars.lookup name = some (shape,names) ∧
      names.length = sizeOfShapeHOL shape := by
  simp [valueDeclContext,FUPDATE]

theorem valueDecl_compiled {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (declared : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width) (shape : ShapeHOL)
    (values : List (CrepExpHOL width)) (compiled : compileExpExactHOLW ctxt initializer = (values,shape))
    (size : sizeOfShapeHOL shape = values.length) :
    compileProgExactHOLW ctxt (.dec name declared initializer body) =
      nestedDecsHOL ((List.range (sizeOfShapeHOL shape)).map (fun index => ctxt.vmax + index + 1))
        values (compileProgExactHOLW (valueDeclContext ctxt name shape) body) := by
  simp [compileProgExactHOLW,compileDecExactHOLW,compiled,size,valueDeclContext]

/-- The body of a scalar declaration is compiled under the fresh local binding
allocated by the actual Pancake-to-Crep compiler. -/
def scalarDeclContext {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) : PanToCrepContextExact width :=
  { ctxt with vars := ctxt.vars.update (name,(.one,[ctxt.vmax+1])), vmax := ctxt.vmax+1 }

theorem scalarDeclContext_eq_value {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) (name : MlS) :
    scalarDeclContext ctxt name = valueDeclContext ctxt name .one := by
  simp [scalarDeclContext,valueDeclContext,sizeOfShapeHOL]


/-- The newly declared scalar is available to the body as a singleton local. -/
theorem scalarDeclContext_local {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) :
    (scalarDeclContext ctxt name).vars.lookup name = some (.one,[ctxt.vmax+1]) := by
  have h := valueDeclContext_local ctxt name .one
  simpa [← scalarDeclContext_eq_value,sizeOfShapeHOL] using h.1

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
  have result := valueDecl_compiled ctxt name .one initializer body .one [value] compiled (by rfl)
  simpa [← scalarDeclContext_eq_value,sizeOfShapeHOL,nestedDecsHOL] using result

end SteppedFlapjack.PanToCrepSteps
