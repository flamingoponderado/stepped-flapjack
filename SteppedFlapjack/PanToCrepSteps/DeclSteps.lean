import SteppedFlapjack.PanToCrepSteps.DeclShape
import SteppedFlapjack.PanToCrepSteps.BranchWhile

/-! Quantitative compilation of a scalar declaration enclosing a loop. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- A successfully initialized scalar declaration adds one target visit to the
bound for its initialized loop and continuation. -/
theorem scalarDecl_loop_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (name : MlS) (initializer : ExpHOL width) (init : ProgHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (context : PanToCrepContextExact width)
    (initializerShape : ScalarExpression context initializer)
    (initShape : BranchProgram (scalarDeclContext context name) init)
    (conditionShape : ScalarExpression (scalarDeclContext context name) condition)
    (bodyShape : BranchProgram (scalarDeclContext context name) body)
    (tailShape : BranchProgram (scalarDeclContext context name) tail)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ) (w : BitVec width)
    (evaluated : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) initializer = some (.val (.word w)))
    (run : (PanSemStateFiniteExact.setVarHOLFinite name (.val (.word w)) source).evaluateHOLFiniteState
      (.seq init (.seq (.while condition body) tail)) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) = true) :
    CrepSteps.steps (compileProgExactHOLW context (.dec name .one initializer
      (.seq init (.seq (.while condition body) tail)))) target ≤
      (4 + sizeOf (compileProgExactHOLW (scalarDeclContext context name) init) +
        sizeOf (compileProgExactHOLW (scalarDeclContext context name) body) +
        sizeOf (compileProgExactHOLW (scalarDeclContext context name) tail)) *
        controlSteps (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) source := by
  classical
  have locs : localisedExpHOL initializer = true ∧
      localisedProgHOL (.seq init (.seq (.while condition body) tail)) = true := by
    simpa [localisedProgHOL] using localised
  obtain ⟨ce, compiled, direct⟩ := scalar_compile initializerShape
  have hce : evalCrepSemHOLExp target ce = some (.word w) := by
    have h := @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) context target
      (fun address => Classical.propDecidable (target.memaddrs address))
      initializer (.val (.word w)) [ce] .one evaluated stateRel codeRel localsRel locs.1 compiled
    obtain ⟨values,_,_,_⟩ := h
    simpa [flattenHOL] using values
  have innerLocals := localsRelExtendNewVarHOL context source.locals target.locals
    (.val (.word w)) name [context.vmax+1] (by
      refine ⟨localsRel, ?_, ?_, ?_, ?_⟩ <;> simp [shapeOfHOLExact])
  have innerState : panToCrepStateRelFiniteExact
      (PanSemStateFiniteExact.setVarHOLFinite name (.val (.word w)) source)
      (CrepSemHOLState.setVar (context.vmax+1) (.word w) target) := by
    simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setVarHOLFinite,
      CrepSemHOLState.setVar] using stateRel
  have singletonUpdate : target.locals.updateListEq [(context.vmax+1, .word w)] =
      target.locals.updateEq (context.vmax+1, .word w) := by
    apply HolFiniteMapExact.ext
    funext k
    rfl
  have innerLocals' : panToCrepLocalsRelFiniteExact (scalarDeclContext context name)
      (PanSemStateFiniteExact.setVarHOLFinite name (.val (.word w)) source).locals
      (CrepSemHOLState.setVar (context.vmax+1) (.word w) target).locals := by
    simpa [scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite, CrepSemHOLState.setVar,
      shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeHOL, flattenHOL,
      singletonUpdate] using innerLocals
  have bound := branchWhileBranch_compiled_steps init condition body tail (scalarDeclContext context name)
    initShape conditionShape bodyShape tailShape _ sourceFinal result _ run nonerror innerState
    (by simpa [codeRelExactHOLW, scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite, CrepSemHOLState.setVar] using codeRel)
    (by simpa [scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite] using excpRel)
    innerLocals' locs.2
  have count := controlSteps_dec name .one initializer (.seq init (.seq (.while condition body) tail))
    source (.val (.word w)) evaluated (by simp [shapeEqHOL,shapeOfHOLExact])
  obtain ⟨value,_,comp⟩ := scalarDecl_compile context name initializer _ initializerShape
  have valueEq : value = ce := by
    simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext] at comp
    exact comp.symm
  subst value
  rw [comp,CrepSteps.steps_dec,hce,count]
  simp only
  nlinarith

end SteppedFlapjack.PanToCrepSteps
