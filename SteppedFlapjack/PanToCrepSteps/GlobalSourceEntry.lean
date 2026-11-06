import SteppedFlapjack.PanToCrepSteps.GlobalWhile
import SteppedFlapjack.PanToCrepSteps.GlobalPanCodeRel

/-! Connect an original initialized loop to the generated global entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

/-- The globals state relation and the source code lookup identify the actual
lowered callee in the compiler's function table after initialization. -/
theorem globalEntry_lowered_callee_lookup {width : Nat} [NeZero width] {σ : Type}
    (declarations : List (DeclHOL width)) (start : MlString) (init : ProgHOL width)
    (globals : PanGlobalsContextExact width) (pan middle source : PanSemStateFiniteExact width σ)
    (body : ProgHOL width) (returnShape : ShapeHOL)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState init = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],body,returnShape))
    (rel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty)) :
    (functionsHOL (compileTopExactHOL declarations start)).lookup (newMainNameHOL declarations) =
      some ([],compileProgExactHOL globals body,returnShape) := by
  have codeRel := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have targetFound := codeRel (newMainNameHOL declarations) [] body returnShape sourceFound
  have middleFound : middle.code.lookup (newMainNameHOL declarations) =
      some ([],compileProgExactHOL globals body,returnShape) := by
    simpa only [callEntryStateHOLFinite,decClockHOLFinite] using targetFound
  have preserved : middle.code = pan.code := by
    have h := SemInitSupport.eval_code pan init
    rw [initRun] at h
    exact h
  rw [preserved,panCode] at middleFound
  change Flapjack.FLOOKUP (Flapjack.FUPDATE_LIST Flapjack.FEMPTY
    (functionsHOL (compileTopExactHOL declarations start)).reverse) (newMainNameHOL declarations) = _ at middleFound
  rw [Flapjack.FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at middleFound
  exact middleFound


/-- Given the original callee lookup and a related original state,
its non-error source run supplies both the lowered run and the entry bound
required by the downstream machine theorem. -/
theorem globalEntry_originalLoop_with_steps {width : Nat} [NeZero width] {σ : Type}
    (declarations : List (DeclHOL width)) (start : MlString) (initializers : List (ProgHOL width))
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (init : ProgHOL width) (condition : ExpHOL width) (body tail : ProgHOL width)
    (initShape : BranchProgram ctxt init) (conditionShape : ScalarExpression ctxt condition)
    (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail)
    (pan middle source sourceFinal : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (returnShape : ShapeHOL)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) =
      some ([],.seq init (.seq (.while condition body) tail),returnShape))
    (clock : middle.clock ≠ 0)
    (run : source.evaluateHOLFiniteState (.seq init (.seq (.while condition body) tail)) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty)) :
    ∃ loweredFinal,
      (functionsHOL (compileTopExactHOL declarations start)).lookup (newMainNameHOL declarations) =
        some ([],.seq (compileProgExactHOL globals init)
          (.seq (.while (compileExpExactHOL globals condition) (compileProgExactHOL globals body))
            (compileProgExactHOL globals tail)),returnShape) ∧
      BranchProgram ctxt (compileProgExactHOL globals init) ∧
      ScalarExpression ctxt (compileExpExactHOL globals condition) ∧
      BranchProgram ctxt (compileProgExactHOL globals body) ∧
      BranchProgram ctxt (compileProgExactHOL globals tail) ∧
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty).evaluateHOLFiniteState
        (.seq (compileProgExactHOL globals init)
          (.seq (.while (compileExpExactHOL globals condition) (compileProgExactHOL globals body))
            (compileProgExactHOL globals tail))) = (result,loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL result) globals sourceFinal loweredFinal ∧
      globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL declarations) [] pan ≤
        controlSteps (nestedSeqHOL initializers) pan +
          (3 + sizeOf (compileProgExactHOL globals init) + sizeOf (compileProgExactHOL globals body) +
            sizeOf (compileProgExactHOL globals tail)) *
          controlSteps (.seq init (.seq (.while condition body) tail)) source + 2 := by
  obtain ⟨loweredFinal,loweredRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.seq init (.seq (.while condition body) tail)) source result globals
    (callEntryStateHOLFinite middle HolFiniteMapExact.empty) sourceFinal ⟨rel,run,nonerror⟩
  have found := globalEntry_lowered_callee_lookup declarations start (nestedSeqHOL initializers)
    globals pan middle source (.seq init (.seq (.while condition body) tail)) returnShape panCode initRun sourceFound rel
  have lookup := global_lowered_lookup_after_init declarations start (newMainNameHOL declarations)
    pan middle (nestedSeqHOL initializers) _ returnShape panCode initRun found
  have bodyBound := globalCompile_initializedLoop_steps globals ctxt init condition body tail initShape bodyShape tailShape
    source sourceFinal (callEntryStateHOLFinite middle HolFiniteMapExact.empty) result run nonerror rel
  have entryBound := globalEntrySteps_bound (nestedSeqHOL initializers) (newMainNameHOL declarations) []
    pan middle [] _ HolFiniteMapExact.empty returnShape _ initRun (by rfl) lookup clock bodyBound
  refine ⟨loweredFinal,?_,globalCompile_branch_shape globals initShape,
    globalCompile_scalar_shape globals conditionShape,globalCompile_branch_shape globals bodyShape,
    globalCompile_branch_shape globals tailShape,?_,postRel,entryBound⟩
  · simpa only [compileProgExactHOL] using found
  · simpa only [compileProgExactHOL] using loweredRun



end SteppedFlapjack.PanToCrepSteps
