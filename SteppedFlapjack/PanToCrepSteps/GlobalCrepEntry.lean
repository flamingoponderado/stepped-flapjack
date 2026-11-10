import SteppedFlapjack.PanToCrepSteps.GlobalEntry
import SteppedFlapjack.CrepToLoopSteps.InlineEntry

/-! Connect the actual global-entry wrapper to its Crep compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.CrepToLoopSteps

/-- If the generated initializer is in the supported branch fragment and the
renamed main is not inline-marked, the actual compiled entry retains the
initializer and tail call, with exactly the same Crep execution count. -/
theorem globalEntry_nonInline_preserved {width : Nat} [NeZero width] {σ : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (initializers : List (ProgHOL width)) (returnShape : ShapeHOL)
    (original : ProgHOL width)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL width)) (context : PanGlobalsContextExact width)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (initShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)))
    (notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (state : CrepSemHOLState width σ) :
    let lowered := compileTopExactHOL declarations start
    let ctxt : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW ctxt (nestedSeqHOL initializers)
    ∃ h : 0 < (compileProgDeclsHOLW lowered).length,
      (compileProgDeclsHOLW lowered)[0]'h = (start,[],.seq init (.call none (newMainNameHOL declarations) [])) ∧
      CrepSteps.steps ((compileProgDeclsHOLW lowered)[0]'h).2.2 state =
        CrepSteps.steps (.seq init (.call none (newMainNameHOL declarations) [])) state := by
  obtain ⟨is,fs,es,ctx,hcompile,htop⟩ := compileTop_entry_wrapper declarations start [] original returnShape found
  have heq : (initializers,funs,exns,context) = (is,fs,es,ctx) := compiled.symm.trans hcompile
  cases heq
  have noFunctions : functionsHOL exns = [] := by
    rw [PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ hcompile]
    exact PanGlobalsDeclListExact.functions_FILTER_exn_declHOL _
  have first : functionsHOL (compileTopExactHOL declarations start) =
      (start,[],.seq (nestedSeqHOL initializers) (.call none (newMainNameHOL declarations) []),returnShape) :: functionsHOL funs := by
    rw [htop,functionsHOL_append,noFunctions]
    rfl
  let lowered := compileTopExactHOL declarations start
  let ctxt : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
  let init := compileProgExactHOLW ctxt (nestedSeqHOL initializers)
  have hi : 0 < (compileToCrepExactHOLW lowered).length := by
    simp [compileToCrepExactHOLW,lowered,first]
  have entry : (compileToCrepExactHOLW lowered)[0] =
      (start,[],.seq init (.call none (newMainNameHOL declarations) [])) := by
    simp only [compileToCrepExactHOLW,lowered,List.getElem_map,first,List.getElem_cons_zero,
      crepVarsHOL,List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,List.range_zero,compFuncExactHOLW,Nat.zero_sub,
      compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil,init,ctxt]
  exact compileProgDecls_tailEntry_at lowered 0 hi start (newMainNameHOL declarations) init initShape [] entry notInline state

end SteppedFlapjack.PanToCrepSteps
