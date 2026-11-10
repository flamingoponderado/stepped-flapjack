import SteppedFlapjack.PanToCrepSteps.GlobalWhile
import SteppedFlapjack.PanToCrepSteps.DeclSteps
import SteppedFlapjack.PanToCrepSteps.GlobalSourceEntry

/-! Global lowering preserves the quantitative bound for a scalar declaration
around an initialized loop. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

/-- Global lowering of a non-error declaration-wrapped loop has a visit bound
in terms of the original declaration execution. -/
theorem globalCompile_declLoop_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (name : MlS) (initializer : ExpHOL width) (init : ProgHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (initShape : BranchProgram ctxt init) (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail)
    (source sourceFinal target : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (run : source.evaluateHOLFiniteState (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) =
      (result,sourceFinal)) (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true globals source target) :
    controlSteps (compileProgExactHOL globals (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))) target ≤
      (4 + sizeOf (compileProgExactHOL globals init) + sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals tail)) *
      controlSteps (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) source := by
  classical
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) initializer with
  | none =>
    simp only [heval] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    simp only [heval] at run
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · simp only [valid,ite_true] at run
      have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source initializer value globals target ⟨rel,heval⟩
      have targetEvalExact : @evalHOLExact width σ _ target.toExact
          (fun a => Classical.propDecidable (target.memaddrs a)) (compileExpExactHOL globals initializer) = some value := targetEval
      have bodyRel := PanGlobalsStateRelationLocals.stateRelSetVarHOL globals source target true name value rel
      rcases bodyRun : (setVarHOLFinite name value source).evaluateHOLFiniteState
          (.seq init (.seq (.while condition body) tail)) with ⟨bodyResult,bodyFinal⟩
      rw [bodyRun] at run
      have sameResult : bodyResult = result := (Prod.mk.inj run).1
      subst result
      have bodyBound := globalCompile_initializedLoop_steps globals ctxt init condition body tail initShape bodyShape tailShape
        (setVarHOLFinite name value source) bodyFinal (setVarHOLFinite name value target) bodyResult
        bodyRun nonerror bodyRel
      have sourceCount := controlSteps_dec name .one initializer (.seq init (.seq (.while condition body) tail)) source value heval valid
      have targetCount := controlSteps_dec name .one (compileExpExactHOL globals initializer)
        (compileProgExactHOL globals (.seq init (.seq (.while condition body) tail))) target value targetEvalExact valid
      rw [compileProgExactHOL,targetCount,sourceCount]
      nlinarith
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

/-- The actual compiled Crep declaration is bounded by the original source
visits through both global lowering and Pancake-to-Crep compilation. -/
theorem globalCompile_declLoop_crep_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (name : MlS) (initializer : ExpHOL width) (init : ProgHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (initializerShape : ScalarExpression ctxt initializer)
    (initShape : BranchProgram (scalarDeclContext ctxt name) init)
    (conditionShape : ScalarExpression (scalarDeclContext ctxt name) condition)
    (bodyShape : BranchProgram (scalarDeclContext ctxt name) body)
    (tailShape : BranchProgram (scalarDeclContext ctxt name) tail)
    (source sourceFinal lowered : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (crep : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) =
      (result,sourceFinal)) (nonerror : result ≠ some .error)
    (globalRel : panGlobalsStateRelHOLExact true globals source lowered)
    (stateRel : panToCrepStateRelFiniteExact lowered crep)
    (codeRel : codeRelExactHOLW ctxt lowered.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids lowered.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt lowered.locals crep.locals)
    (localised : localisedProgHOL (compileProgExactHOL globals
      (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))) = true) :
    let inner := scalarDeclContext ctxt name
    CrepSteps.steps (compileProgExactHOLW ctxt (compileProgExactHOL globals
      (.dec name .one initializer (.seq init (.seq (.while condition body) tail))))) crep ≤
      ((4 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals init)) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals body)) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals tail))) *
       (4 + sizeOf (compileProgExactHOL globals init) + sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals tail))) *
      controlSteps (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) source := by
  obtain ⟨loweredFinal,loweredRun,_⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))
    source result globals lowered sourceFinal ⟨globalRel,run,nonerror⟩
  have sourceBound := globalCompile_declLoop_steps globals (scalarDeclContext ctxt name) name initializer
    init condition body tail initShape bodyShape tailShape source sourceFinal lowered result run nonerror globalRel
  have crepBound := scalarDecl_loop_run_compiled_steps name (compileExpExactHOL globals initializer)
    (compileProgExactHOL globals init) (compileExpExactHOL globals condition)
    (compileProgExactHOL globals body) (compileProgExactHOL globals tail) ctxt
    (globalCompile_scalar_shape globals initializerShape) (globalCompile_branch_shape globals initShape)
    (globalCompile_scalar_shape globals conditionShape) (globalCompile_branch_shape globals bodyShape)
    (globalCompile_branch_shape globals tailShape) lowered loweredFinal result crep
    (by simpa only [compileProgExactHOL] using loweredRun) nonerror stateRel codeRel excpRel localsRel
    (by simpa only [compileProgExactHOL] using localised)
  simp only [compileProgExactHOL] at sourceBound
  simpa only [compileProgExactHOL, Nat.mul_assoc] using crepBound.trans (Nat.mul_le_mul_left _ sourceBound)

/-- The original declaration-wrapped loop yields its actual lowered callee
lookup, execution, final-state relation, and global entry cost bound. -/
theorem globalEntry_originalDeclLoop_with_steps {width : Nat} [NeZero width] {σ : Type}
    (declarations : List (DeclHOL width)) (start : MlString) (initializers : List (ProgHOL width))
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (name : MlS) (initializer : ExpHOL width) (init : ProgHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (initShape : BranchProgram ctxt init) (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail)
    (pan middle source sourceFinal : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (returnShape : ShapeHOL)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) =
      some ([],.dec name .one initializer (.seq init (.seq (.while condition body) tail)),returnShape))
    (clock : middle.clock ≠ 0)
    (run : source.evaluateHOLFiniteState (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) =
      (result,sourceFinal)) (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty)) :
    ∃ loweredFinal,
      (functionsHOL (compileTopExactHOL declarations start)).lookup (newMainNameHOL declarations) =
        some ([],.dec name .one (compileExpExactHOL globals initializer)
          (.seq (compileProgExactHOL globals init)
            (.seq (.while (compileExpExactHOL globals condition) (compileProgExactHOL globals body))
              (compileProgExactHOL globals tail))),returnShape) ∧
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty).evaluateHOLFiniteState
        (compileProgExactHOL globals (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))) =
        (result,loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL result) globals sourceFinal loweredFinal ∧
      globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL declarations) [] pan ≤
        controlSteps (nestedSeqHOL initializers) pan +
          (4 + sizeOf (compileProgExactHOL globals init) + sizeOf (compileProgExactHOL globals body) +
            sizeOf (compileProgExactHOL globals tail)) *
          controlSteps (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) source + 2 := by
  obtain ⟨loweredFinal,loweredRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.dec name .one initializer (.seq init (.seq (.while condition body) tail))) source result globals
    (callEntryStateHOLFinite middle HolFiniteMapExact.empty) sourceFinal ⟨rel,run,nonerror⟩
  have found := globalEntry_lowered_callee_lookup declarations start (nestedSeqHOL initializers)
    globals pan middle source (.dec name .one initializer (.seq init (.seq (.while condition body) tail)))
    returnShape panCode initRun sourceFound rel
  have lookup := global_lowered_lookup_after_init declarations start (newMainNameHOL declarations)
    pan middle (nestedSeqHOL initializers) _ returnShape panCode initRun found
  have bodyBound := globalCompile_declLoop_steps globals ctxt name initializer init condition body tail
    initShape bodyShape tailShape source sourceFinal (callEntryStateHOLFinite middle HolFiniteMapExact.empty)
    result run nonerror rel
  have entryBound := globalEntrySteps_bound (nestedSeqHOL initializers) (newMainNameHOL declarations) []
    pan middle [] _ HolFiniteMapExact.empty returnShape _ initRun (by rfl) lookup clock bodyBound
  refine ⟨loweredFinal,?_,loweredRun,postRel,entryBound⟩
  simpa only [compileProgExactHOL] using found

/-- Global lowering of a non-error declaration-wrapped loop has a visit bound
in terms of the original declaration execution. -/
theorem globalCompile_declWhile_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (name : MlS) (initializer : ExpHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail)
    (source sourceFinal target : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (run : source.evaluateHOLFiniteState (.dec name .one initializer (.seq (.while condition body) tail)) =
      (result,sourceFinal)) (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true globals source target) :
    controlSteps (compileProgExactHOL globals (.dec name .one initializer (.seq (.while condition body) tail))) target ≤
      (3 + sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals tail)) *
      controlSteps (.dec name .one initializer (.seq (.while condition body) tail)) source := by
  classical
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) initializer with
  | none =>
    simp only [heval] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    simp only [heval] at run
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · simp only [valid,ite_true] at run
      have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source initializer value globals target ⟨rel,heval⟩
      have targetEvalExact : @evalHOLExact width σ _ target.toExact
          (fun a => Classical.propDecidable (target.memaddrs a)) (compileExpExactHOL globals initializer) = some value := targetEval
      have bodyRel := PanGlobalsStateRelationLocals.stateRelSetVarHOL globals source target true name value rel
      rcases bodyRun : (setVarHOLFinite name value source).evaluateHOLFiniteState
          (.seq (.while condition body) tail) with ⟨bodyResult,bodyFinal⟩
      rw [bodyRun] at run
      have sameResult : bodyResult = result := (Prod.mk.inj run).1
      subst result
      have bodyBound := globalCompile_whileThenBranch_steps globals ctxt condition body tail bodyShape tailShape
        (setVarHOLFinite name value source) bodyFinal (setVarHOLFinite name value target) bodyResult
        bodyRun nonerror bodyRel
      have sourceCount := controlSteps_dec name .one initializer (.seq (.while condition body) tail) source value heval valid
      have targetCount := controlSteps_dec name .one (compileExpExactHOL globals initializer)
        (compileProgExactHOL globals (.seq (.while condition body) tail)) target value targetEvalExact valid
      rw [compileProgExactHOL,targetCount,sourceCount]
      nlinarith
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

/-- The actual compiled Crep declaration is bounded by the original source
visits through both global lowering and Pancake-to-Crep compilation. -/
theorem globalCompile_declWhile_crep_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (name : MlS) (initializer : ExpHOL width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (initializerShape : ScalarExpression ctxt initializer)
    (conditionShape : ScalarExpression (scalarDeclContext ctxt name) condition)
    (bodyShape : BranchProgram (scalarDeclContext ctxt name) body)
    (tailShape : BranchProgram (scalarDeclContext ctxt name) tail)
    (source sourceFinal lowered : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (crep : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.dec name .one initializer (.seq (.while condition body) tail)) =
      (result,sourceFinal)) (nonerror : result ≠ some .error)
    (globalRel : panGlobalsStateRelHOLExact true globals source lowered)
    (stateRel : panToCrepStateRelFiniteExact lowered crep)
    (codeRel : codeRelExactHOLW ctxt lowered.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids lowered.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt lowered.locals crep.locals)
    (localised : localisedProgHOL (compileProgExactHOL globals
      (.dec name .one initializer (.seq (.while condition body) tail))) = true) :
    let inner := scalarDeclContext ctxt name
    CrepSteps.steps (compileProgExactHOLW ctxt (compileProgExactHOL globals
      (.dec name .one initializer (.seq (.while condition body) tail)))) crep ≤
      ((3 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals body)) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals tail))) *
       (3 + sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals tail))) *
      controlSteps (.dec name .one initializer (.seq (.while condition body) tail)) source := by
  obtain ⟨loweredFinal,loweredRun,_⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.dec name .one initializer (.seq (.while condition body) tail))
    source result globals lowered sourceFinal ⟨globalRel,run,nonerror⟩
  have sourceBound := globalCompile_declWhile_steps globals (scalarDeclContext ctxt name) name initializer
    condition body tail bodyShape tailShape source sourceFinal lowered result run nonerror globalRel
  have crepBound := scalarDecl_whileThenBranch_run_compiled_steps name (compileExpExactHOL globals initializer)
    (compileExpExactHOL globals condition)
    (compileProgExactHOL globals body) (compileProgExactHOL globals tail) ctxt
    (globalCompile_scalar_shape globals initializerShape)
    (globalCompile_scalar_shape globals conditionShape) (globalCompile_branch_shape globals bodyShape)
    (globalCompile_branch_shape globals tailShape) lowered loweredFinal result crep
    (by simpa only [compileProgExactHOL] using loweredRun) nonerror stateRel codeRel excpRel localsRel
    (by simpa only [compileProgExactHOL] using localised)
  simp only [compileProgExactHOL] at sourceBound
  simpa only [compileProgExactHOL, Nat.mul_assoc] using crepBound.trans (Nat.mul_le_mul_left _ sourceBound)

end SteppedFlapjack.PanToCrepSteps
