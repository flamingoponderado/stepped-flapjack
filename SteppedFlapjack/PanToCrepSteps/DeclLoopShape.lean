import SteppedFlapjack.PanToCrepSteps.DeclShape
import SteppedFlapjack.PanToCrepSteps.ConditionShape
import SteppedFlapjack.CrepToLoopSteps.InlineSupported

/-! Supported declaration-wrapped loops through the actual frontend. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.CrepToLoopSteps

/-- A scalar local declaration around an initialized loop and continuation
compiles to a supported Crep function body, in the compiler's fresh context. -/
theorem scalarDeclLoop_supported {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (initializer condition : ExpHOL width)
    (init body tail : ProgHOL width) (initializerShape : ScalarExpression ctxt initializer)
    (initShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) init)
    (conditionShape : PanToCrepSteps.BranchCondition (scalarDeclContext ctxt name) condition)
    (bodyShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) body)
    (tailShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) tail) :
    SupportedCodeBody (compileProgExactHOLW ctxt
      (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))) := by
  obtain ⟨value,direct,declCompiled⟩ := scalarDecl_compile ctxt name initializer
    (.seq init (.seq (.while condition body) tail)) initializerShape
  obtain ⟨ce,conditionCompiled,conditionCrep⟩ := branchCondition_compile conditionShape
  rw [declCompiled]
  have loopCompiled : compileProgExactHOLW (scalarDeclContext ctxt name)
      (.seq init (.seq (.while condition body) tail)) =
      .seq (compileProgExactHOLW (scalarDeclContext ctxt name) init)
        (.seq (.while ce (compileProgExactHOLW (scalarDeclContext ctxt name) body))
          (compileProgExactHOLW (scalarDeclContext ctxt name) tail)) := by
    simp [compileProgExactHOLW,compileWhileExactHOLW,conditionCompiled]
  rw [loopCompiled]
  exact .declLoop direct (branch_compile initShape) conditionCrep (branch_compile bodyShape) (branch_compile tailShape)


/-- A scalar declaration around a loop and continuation compiles to a supported body. -/
theorem scalarDeclWhile_supported {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (initializer condition : ExpHOL width)
    (body tail : ProgHOL width) (initializerShape : ScalarExpression ctxt initializer)
    (conditionShape : PanToCrepSteps.BranchCondition (scalarDeclContext ctxt name) condition)
    (bodyShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) body)
    (tailShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) tail) :
    SupportedCodeBody (compileProgExactHOLW ctxt
      (.dec name .one initializer (.seq (.while condition body) tail))) := by
  obtain ⟨value,direct,declCompiled⟩ := scalarDecl_compile ctxt name initializer
    (.seq (.while condition body) tail) initializerShape
  obtain ⟨ce,conditionCompiled,conditionCrep⟩ := branchCondition_compile conditionShape
  rw [declCompiled]
  have loopCompiled : compileProgExactHOLW (scalarDeclContext ctxt name)
      (.seq (.while condition body) tail) =
      .seq (.while ce (compileProgExactHOLW (scalarDeclContext ctxt name) body))
        (compileProgExactHOLW (scalarDeclContext ctxt name) tail) := by
    simp [compileProgExactHOLW,compileWhileExactHOLW,conditionCompiled]
  rw [loopCompiled]
  exact .declWhile direct conditionCrep (branch_compile bodyShape) (branch_compile tailShape)

/-- A fresh local initialized to one can be tested and set to zero inside a
loop, even when the outer compiler context has no local bindings. -/
theorem scalarDeclLoop_set_zero_supported {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (returned : BitVec width) :
    SupportedCodeBody (compileProgExactHOLW ctxt
      (.dec name .one (.const 1)
        (.seq .skip (.seq (.while (.var .local name) (.assign .local name (.const 0)))
          (.return (.const returned)))))) := by
  have localFound := scalarDeclContext_local ctxt name
  exact scalarDeclLoop_supported ctxt name (.const 1) (.var .local name)
    .skip (.assign .local name (.const 0)) (.return (.const returned)) (.const 1)
    .skip (.scalar (.local name _ localFound)) (.assign name _ localFound (.const 0)) (.return (.const returned))

/-- Actual compiler output and all frontend shapes for a scalar declaration
around an initialized loop with a direct scalar condition. -/
theorem scalarDeclLoop_compiled_shapes {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (initializer condition : ExpHOL width)
    (init body tail : ProgHOL width) (initializerShape : ScalarExpression ctxt initializer)
    (initShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) init)
    (conditionShape : ScalarExpression (scalarDeclContext ctxt name) condition)
    (bodyShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) body)
    (tailShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) tail) :
    ∃ value test,
      compileExpExactHOLW ctxt initializer = ([value],.one) ∧ DirectExpression value ∧
      compileExpExactHOLW (scalarDeclContext ctxt name) condition = ([test],.one) ∧ DirectExpression test ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW (scalarDeclContext ctxt name) init) ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW (scalarDeclContext ctxt name) body) ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW (scalarDeclContext ctxt name) tail) ∧
      compileProgExactHOLW ctxt (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) =
        .dec (ctxt.vmax+1) value (.seq (compileProgExactHOLW (scalarDeclContext ctxt name) init)
          (.seq (.while test (compileProgExactHOLW (scalarDeclContext ctxt name) body))
            (compileProgExactHOLW (scalarDeclContext ctxt name) tail))) := by
  obtain ⟨value,compiledValue,directValue⟩ := scalar_compile initializerShape
  obtain ⟨test,compiledTest,directTest⟩ := scalar_compile conditionShape
  refine ⟨value,test,compiledValue,directValue,compiledTest,directTest,
    branch_compile initShape,branch_compile bodyShape,branch_compile tailShape,?_⟩
  obtain ⟨v,_,declCompiled⟩ := scalarDecl_compile ctxt name initializer
    (.seq init (.seq (.while condition body) tail)) initializerShape
  have valueEq : v = value := by
    simp [compileProgExactHOLW,compileDecExactHOLW,compiledValue,nestedDecsHOL,scalarDeclContext] at declCompiled
    exact declCompiled.symm
  subst v
  rw [declCompiled]
  simp [compileProgExactHOLW,compileWhileExactHOLW,compiledTest]

/-- Actual compiler output and all frontend shapes for a scalar declaration
around an initialized loop with a direct scalar condition. -/
theorem scalarDeclWhile_compiled_shapes {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) (initializer condition : ExpHOL width)
    (body tail : ProgHOL width) (initializerShape : ScalarExpression ctxt initializer)
    (conditionShape : ScalarExpression (scalarDeclContext ctxt name) condition)
    (bodyShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) body)
    (tailShape : PanToCrepSteps.BranchProgram (scalarDeclContext ctxt name) tail) :
    ∃ value test,
      compileExpExactHOLW ctxt initializer = ([value],.one) ∧ DirectExpression value ∧
      compileExpExactHOLW (scalarDeclContext ctxt name) condition = ([test],.one) ∧ DirectExpression test ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW (scalarDeclContext ctxt name) body) ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW (scalarDeclContext ctxt name) tail) ∧
      compileProgExactHOLW ctxt (.dec name .one initializer (.seq (.while condition body) tail)) =
        .dec (ctxt.vmax+1) value (.seq (.while test (compileProgExactHOLW (scalarDeclContext ctxt name) body))
            (compileProgExactHOLW (scalarDeclContext ctxt name) tail)) := by
  obtain ⟨value,compiledValue,directValue⟩ := scalar_compile initializerShape
  obtain ⟨test,compiledTest,directTest⟩ := scalar_compile conditionShape
  refine ⟨value,test,compiledValue,directValue,compiledTest,directTest,
    branch_compile bodyShape,branch_compile tailShape,?_⟩
  obtain ⟨v,_,declCompiled⟩ := scalarDecl_compile ctxt name initializer
    (.seq (.while condition body) tail) initializerShape
  have valueEq : v = value := by
    simp [compileProgExactHOLW,compileDecExactHOLW,compiledValue,nestedDecsHOL,scalarDeclContext] at declCompiled
    exact declCompiled.symm
  subst v
  rw [declCompiled]
  simp [compileProgExactHOLW,compileWhileExactHOLW,compiledTest]

end SteppedFlapjack.PanToCrepSteps
