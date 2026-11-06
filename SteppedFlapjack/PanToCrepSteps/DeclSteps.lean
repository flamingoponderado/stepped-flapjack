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
    (target : CrepSemHOLState width σ) (w : HolWordLab width)
    (evaluated : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) initializer = some (.val w))
    (run : (PanSemStateFiniteExact.setVarHOLFinite name (.val w) source).evaluateHOLFiniteState
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
  have hce : evalCrepSemHOLExp target ce = some w := by
    have h := @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) context target
      (fun address => Classical.propDecidable (target.memaddrs address))
      initializer (.val w) [ce] .one evaluated stateRel codeRel localsRel locs.1 compiled
    obtain ⟨values,_,_,_⟩ := h
    simpa [flattenHOL] using values
  have innerLocals := localsRelExtendNewVarHOL context source.locals target.locals
    (.val w) name [context.vmax+1] (by
      refine ⟨localsRel, ?_, ?_, ?_, ?_⟩ <;> simp [shapeOfHOLExact])
  have innerState : panToCrepStateRelFiniteExact
      (PanSemStateFiniteExact.setVarHOLFinite name (.val w) source)
      (CrepSemHOLState.setVar (context.vmax+1) w target) := by
    simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setVarHOLFinite,
      CrepSemHOLState.setVar] using stateRel
  have singletonUpdate : target.locals.updateListEq [(context.vmax+1, w)] =
      target.locals.updateEq (context.vmax+1, w) := by
    apply HolFiniteMapExact.ext
    funext k
    rfl
  have innerLocals' : panToCrepLocalsRelFiniteExact (scalarDeclContext context name)
      (PanSemStateFiniteExact.setVarHOLFinite name (.val w) source).locals
      (CrepSemHOLState.setVar (context.vmax+1) w target).locals := by
    simpa [scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite, CrepSemHOLState.setVar,
      shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeHOL, flattenHOL,
      singletonUpdate] using innerLocals
  have bound := branchWhileBranch_compiled_steps init condition body tail (scalarDeclContext context name)
    initShape conditionShape bodyShape tailShape _ sourceFinal result _ run nonerror innerState
    (by simpa [codeRelExactHOLW, scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite, CrepSemHOLState.setVar] using codeRel)
    (by simpa [scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite] using excpRel)
    innerLocals' locs.2
  have count := controlSteps_dec name .one initializer (.seq init (.seq (.while condition body) tail))
    source (.val w) evaluated (by simp [shapeEqHOL,shapeOfHOLExact])
  obtain ⟨value,_,comp⟩ := scalarDecl_compile context name initializer _ initializerShape
  have valueEq : value = ce := by
    simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext] at comp
    exact comp.symm
  subst value
  rw [comp,CrepSteps.steps_dec,hce,count]
  simp only
  nlinarith

/-- The quantitative bound follows from the whole non-error declaration run;
the successful scalar initializer and body execution are obtained from the
actual source semantics. -/
theorem scalarDecl_loop_run_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (name : MlS) (initializer : ExpHOL width) (init : ProgHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (context : PanToCrepContextExact width)
    (initializerShape : ScalarExpression context initializer)
    (initShape : BranchProgram (scalarDeclContext context name) init)
    (conditionShape : ScalarExpression (scalarDeclContext context name) condition)
    (bodyShape : BranchProgram (scalarDeclContext context name) body)
    (tailShape : BranchProgram (scalarDeclContext context name) tail)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.dec name .one initializer
      (.seq init (.seq (.while condition body) tail))) = (result,sourceFinal))
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
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) initializer with
  | none =>
    rw [heval] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    rw [heval] at run
    dsimp only at run
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · rw [if_pos valid] at run
      have shape := (shapeEqHOL_eq_true _ _).mp valid
      cases value with
      | val word =>
        rcases bodyRun : (PanSemStateFiniteExact.setVarHOLFinite name (.val word) source).evaluateHOLFiniteState
            (.seq init (.seq (.while condition body) tail)) with ⟨bodyResult,bodyFinal⟩
        rw [bodyRun] at run
        have sameResult : bodyResult = result := (Prod.mk.inj run).1
        subst result
        exact scalarDecl_loop_compiled_steps name initializer init condition body tail context initializerShape
          initShape conditionShape bodyShape tailShape source bodyFinal bodyResult target word heval bodyRun
          nonerror stateRel codeRel excpRel localsRel localised
      | rStruct fields => simp [shapeOfHOLExact] at shape
      | nStruct name fields => simp [shapeOfHOLExact] at shape
    · rw [if_neg valid] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

/-- A scalar declaration around an unprefixed loop has a source-derived Crep bound. -/
theorem scalarDecl_whileThenBranch_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (name : MlS) (initializer : ExpHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (context : PanToCrepContextExact width)
    (initializerShape : ScalarExpression context initializer)
    (conditionShape : ScalarExpression (scalarDeclContext context name) condition)
    (bodyShape : BranchProgram (scalarDeclContext context name) body)
    (tailShape : BranchProgram (scalarDeclContext context name) tail)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ) (w : HolWordLab width)
    (evaluated : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) initializer = some (.val w))
    (run : (PanSemStateFiniteExact.setVarHOLFinite name (.val w) source).evaluateHOLFiniteState
      (.seq (.while condition body) tail) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.dec name .one initializer (.seq (.while condition body) tail)) = true) :
    CrepSteps.steps (compileProgExactHOLW context (.dec name .one initializer
      (.seq (.while condition body) tail))) target ≤
      (3 + sizeOf (compileProgExactHOLW (scalarDeclContext context name) body) +
        sizeOf (compileProgExactHOLW (scalarDeclContext context name) tail)) *
        controlSteps (.dec name .one initializer (.seq (.while condition body) tail)) source := by
  classical
  have locs : localisedExpHOL initializer = true ∧
      localisedProgHOL (.seq (.while condition body) tail) = true := by
    simpa [localisedProgHOL] using localised
  obtain ⟨ce, compiled, direct⟩ := scalar_compile initializerShape
  have hce : evalCrepSemHOLExp target ce = some w := by
    have h := @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) context target
      (fun address => Classical.propDecidable (target.memaddrs address))
      initializer (.val w) [ce] .one evaluated stateRel codeRel localsRel locs.1 compiled
    obtain ⟨values,_,_,_⟩ := h
    simpa [flattenHOL] using values
  have innerLocals := localsRelExtendNewVarHOL context source.locals target.locals
    (.val w) name [context.vmax+1] (by
      refine ⟨localsRel, ?_, ?_, ?_, ?_⟩ <;> simp [shapeOfHOLExact])
  have innerState : panToCrepStateRelFiniteExact
      (PanSemStateFiniteExact.setVarHOLFinite name (.val w) source)
      (CrepSemHOLState.setVar (context.vmax+1) w target) := by
    simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setVarHOLFinite,
      CrepSemHOLState.setVar] using stateRel
  have singletonUpdate : target.locals.updateListEq [(context.vmax+1, w)] =
      target.locals.updateEq (context.vmax+1, w) := by
    apply HolFiniteMapExact.ext
    funext k
    rfl
  have innerLocals' : panToCrepLocalsRelFiniteExact (scalarDeclContext context name)
      (PanSemStateFiniteExact.setVarHOLFinite name (.val w) source).locals
      (CrepSemHOLState.setVar (context.vmax+1) w target).locals := by
    simpa [scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite, CrepSemHOLState.setVar,
      shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeHOL, flattenHOL,
      singletonUpdate] using innerLocals
  have bound := whileThenBranch_compiled_steps condition body tail (scalarDeclContext context name)
    conditionShape bodyShape tailShape _ sourceFinal result _ run nonerror innerState
    (by simpa [codeRelExactHOLW, scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite, CrepSemHOLState.setVar] using codeRel)
    (by simpa [scalarDeclContext, PanSemStateFiniteExact.setVarHOLFinite] using excpRel)
    innerLocals' locs.2
  have count := controlSteps_dec name .one initializer (.seq (.while condition body) tail)
    source (.val w) evaluated (by simp [shapeEqHOL,shapeOfHOLExact])
  obtain ⟨value,_,comp⟩ := scalarDecl_compile context name initializer _ initializerShape
  have valueEq : value = ce := by
    simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext] at comp
    exact comp.symm
  subst value
  rw [comp,CrepSteps.steps_dec,hce,count]
  simp only
  nlinarith

/-- A non-error unprefixed declaration run supplies its compiled Crep bound. -/
theorem scalarDecl_whileThenBranch_run_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (name : MlS) (initializer : ExpHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (context : PanToCrepContextExact width)
    (initializerShape : ScalarExpression context initializer)
    (conditionShape : ScalarExpression (scalarDeclContext context name) condition)
    (bodyShape : BranchProgram (scalarDeclContext context name) body)
    (tailShape : BranchProgram (scalarDeclContext context name) tail)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.dec name .one initializer
      (.seq (.while condition body) tail)) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.dec name .one initializer (.seq (.while condition body) tail)) = true) :
    CrepSteps.steps (compileProgExactHOLW context (.dec name .one initializer
      (.seq (.while condition body) tail))) target ≤
      (3 + sizeOf (compileProgExactHOLW (scalarDeclContext context name) body) +
        sizeOf (compileProgExactHOLW (scalarDeclContext context name) tail)) *
        controlSteps (.dec name .one initializer (.seq (.while condition body) tail)) source := by
  classical
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) initializer with
  | none =>
    rw [heval] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    rw [heval] at run
    dsimp only at run
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · rw [if_pos valid] at run
      have shape := (shapeEqHOL_eq_true _ _).mp valid
      cases value with
      | val word =>
        rcases bodyRun : (PanSemStateFiniteExact.setVarHOLFinite name (.val word) source).evaluateHOLFiniteState
            (.seq (.while condition body) tail) with ⟨bodyResult,bodyFinal⟩
        rw [bodyRun] at run
        have sameResult : bodyResult = result := (Prod.mk.inj run).1
        subst result
        exact scalarDecl_whileThenBranch_compiled_steps name initializer condition body tail context initializerShape
          conditionShape bodyShape tailShape source bodyFinal bodyResult target word heval bodyRun
          nonerror stateRel codeRel excpRel localsRel localised
      | rStruct fields => simp [shapeOfHOLExact] at shape
      | nStruct name fields => simp [shapeOfHOLExact] at shape
    · rw [if_neg valid] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

end SteppedFlapjack.PanToCrepSteps
