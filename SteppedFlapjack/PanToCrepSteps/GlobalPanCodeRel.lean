import SteppedFlapjack.CrepToLoopSteps.InlineSupported
import SteppedFlapjack.PanToCrepSteps.GlobalCodeRelations
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall

/-! Source-to-Crep code relation for the actual global-lowered program. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.CrepToLoopSteps

/-- When the lowered source functions are localized and their compiled bodies
are fixed by the inliner, the source and actual post-inline Crep code tables
satisfy the frontend relation used by the global machine theorem. -/
theorem global_supported_panCrep_codeRel {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (pan : PanSemStateFiniteExact width F) (crep : CrepSemHOLState width F)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL entry.2.2.1 = true)
    (shapes : ∀ name params p, (name,params,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      SupportedCodeBody p)
    (noTail : ∀ name params init callee,
      (name,params,.seq init (.call none callee [])) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst) :
    codeRelExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start)))
        (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
      pan.code crep.code := by
  rw [panCode,crepCode]
  have emptyUpdate : (HolFiniteMapExact.empty.updateList [] : HolFiniteMapExact MlString (ShapeHOL × List Nat)) = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    rfl
  simpa [panToCrepMakeVmapHOLExact, sizeOfShapeHOL, sizeOfShapesHOL, emptyUpdate] using
    supported_compileProgDecls_codeRel (compileTopExactHOL declarations start) unique localised shapes noTail

/-- The same pre-inline syntax facts establish both the Pancake-to-Crep code
relation and the post-inline body shapes needed by the global machine bound. -/
theorem global_supported_panCrep_codeAndShapes {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (pan : PanSemStateFiniteExact width F) (crep : CrepSemHOLState width F)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL entry.2.2.1 = true)
    (shapes : ∀ name params p, (name,params,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      SupportedCodeBody p)
    (noTail : ∀ name params init callee,
      (name,params,.seq init (.call none callee [])) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst) :
    codeRelExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start)))
        (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
      pan.code crep.code ∧
    ∀ name params p, (name,params,p) ∈ compileProgDeclsHOLW (compileTopExactHOL declarations start) →
      SupportedCodeBody p := by
  refine ⟨global_supported_panCrep_codeRel declarations start pan crep panCode crepCode unique localised shapes noTail,?_⟩
  intro name params p member
  have fixed := compileInlTop_supported_fixed
    ((functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (compileToCrepExactHOLW (compileTopExactHOL declarations start)) shapes noTail
  change (name,params,p) ∈ CrepInlineCanonical.compileInlTopHOLExact _ _ at member
  rw [fixed] at member
  exact shapes name params p member

/-- The actual lowered Pancake code table resolves the original zero-argument
start name to the generated initializer and renamed-main tail call. -/
theorem global_lowered_start_lookup {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (original : ProgHOL width) (returnShape : ShapeHOL)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (initializers : List (ProgHOL width)) (funs exns : List (DeclHOL width))
    (context : PanGlobalsContextExact width)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (pan : PanSemStateFiniteExact width F)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse) :
    PanSemStateFiniteExact.lookupCodeHOLFinite pan.code.lookup start [] =
      some (.seq (nestedSeqHOL initializers) (.call none (newMainNameHOL declarations) []),
        HolFiniteMapExact.empty,returnShape) := by
  obtain ⟨is,fs,es,ctx,hcompile,htop⟩ :=
    compileTop_entry_wrapper declarations start [] original returnShape found
  have heq : (initializers,funs,exns,context) = (is,fs,es,ctx) := compiled.symm.trans hcompile
  cases heq
  have noFunctions : functionsHOL exns = [] := by
    rw [PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ hcompile]
    exact PanGlobalsDeclListExact.functions_FILTER_exn_declHOL _
  have first : functionsHOL (compileTopExactHOL declarations start) =
      (start,[],.seq (nestedSeqHOL initializers) (.call none (newMainNameHOL declarations) []),returnShape) :: functionsHOL funs := by
    rw [htop,functionsHOL_append,noFunctions]
    rfl
  apply SemInitSupport.lookup_init
  rw [panCode]
  change Flapjack.FLOOKUP (Flapjack.FUPDATE_LIST Flapjack.FEMPTY
    (functionsHOL (compileTopExactHOL declarations start)).reverse) start = _
  rw [Flapjack.FLOOKUP_FUPDATE_LIST_reverse_eq_lookup,first]
  simp

/-- A completed generated wrapper is the body of the actual lowered start
call. The evaluator performs the outer zero-argument call and clears locals
on return. -/
theorem global_lowered_start_return {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (original : ProgHOL width) (returnShape : ShapeHOL)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (initializers : List (ProgHOL width)) (funs exns : List (DeclHOL width))
    (context : PanGlobalsContextExact width)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (pan post : PanSemStateFiniteExact width F) (value : ValueHOL width)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (clock : pan.clock ≠ 0)
    (run : (PanSemStateFiniteExact.callEntryStateHOLFinite pan HolFiniteMapExact.empty).evaluateHOLFiniteState
      (.seq (nestedSeqHOL initializers) (.call none (newMainNameHOL declarations) [])) = (some (.returned value),post))
    (shape : shapeEqHOL (shapeOfHOLExact value) returnShape = true) :
    pan.evaluateHOLFiniteState (.call none start []) =
      (some (.returned value),PanSemStateFiniteExact.emptyLocalsHOLFinite post) := by
  have lookup := global_lowered_start_lookup declarations start original returnShape found initializers funs exns context compiled pan panCode
  exact evaluateHOLFiniteState_call_return_none pan value start [] [] _
    HolFiniteMapExact.empty returnShape post (by rfl) lookup clock run shape

/-- A successful initializer preserves the actual lowered source code table.
Consequently a zero-argument function found in that table is available at the
callee entry with empty locals. -/
theorem global_lowered_lookup_after_init {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start callee : MlString)
    (pan middle : PanSemStateFiniteExact width F) (init body : ProgHOL width) (returnShape : ShapeHOL)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState init = (none,middle))
    (found : (functionsHOL (compileTopExactHOL declarations start)).lookup callee = some ([],body,returnShape)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite middle.code.lookup callee [] =
      some (body,HolFiniteMapExact.empty,returnShape) := by
  have preserved : middle.code = pan.code := by
    have h := SemInitSupport.eval_code pan init
    rw [initRun] at h
    exact h
  apply SemInitSupport.lookup_init
  rw [preserved,panCode]
  change Flapjack.FLOOKUP (Flapjack.FUPDATE_LIST Flapjack.FEMPTY
    (functionsHOL (compileTopExactHOL declarations start)).reverse) callee = some ([],body,returnShape)
  rw [Flapjack.FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
  exact found

/-- Connect the actual lowered start call to a returned zero-argument
callee and bound the generated wrapper visits by initializer and callee
visits. The outer start call contributes one additional call node. -/
theorem global_lowered_start_return_with_steps {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (original : ProgHOL width) (returnShape : ShapeHOL)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (initializers : List (ProgHOL width)) (funs exns : List (DeclHOL width))
    (context : PanGlobalsContextExact width)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (pan middle final : PanSemStateFiniteExact width F) (callee : ProgHOL width) (calleeShape : ShapeHOL)
    (value : ValueHOL width) (limit : Nat)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (outerClock : pan.clock ≠ 0)
    (initRun : (PanSemStateFiniteExact.callEntryStateHOLFinite pan HolFiniteMapExact.empty).evaluateHOLFiniteState
      (nestedSeqHOL initializers) = (none,middle))
    (calleeFound : (functionsHOL (compileTopExactHOL declarations start)).lookup (newMainNameHOL declarations) =
      some ([],callee,calleeShape))
    (calleeClock : middle.clock ≠ 0)
    (calleeRun : (PanSemStateFiniteExact.callEntryStateHOLFinite middle HolFiniteMapExact.empty).evaluateHOLFiniteState
      callee = (some (.returned value),final))
    (calleeShapeMatch : shapeEqHOL (shapeOfHOLExact value) calleeShape = true)
    (outerShapeMatch : shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (calleeBound : controlSteps callee (PanSemStateFiniteExact.callEntryStateHOLFinite middle HolFiniteMapExact.empty) ≤ limit) :
    pan.evaluateHOLFiniteState (.call none start []) =
      (some (.returned value),PanSemStateFiniteExact.emptyLocalsHOLFinite final) ∧
    1 + globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL declarations) []
      (PanSemStateFiniteExact.callEntryStateHOLFinite pan HolFiniteMapExact.empty) ≤
      controlSteps (nestedSeqHOL initializers) (PanSemStateFiniteExact.callEntryStateHOLFinite pan HolFiniteMapExact.empty) + limit + 3 := by
  let entry := PanSemStateFiniteExact.callEntryStateHOLFinite pan HolFiniteMapExact.empty
  have entryCode : entry.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse := by
    simpa [entry,PanSemStateFiniteExact.callEntryStateHOLFinite,PanSemStateFiniteExact.decClockHOLFinite] using panCode
  have lookup := global_lowered_lookup_after_init declarations start (newMainNameHOL declarations)
    entry middle (nestedSeqHOL initializers) callee calleeShape entryCode initRun calleeFound
  obtain ⟨wrapperRun,wrapperBound⟩ := globalEntry_return_with_steps
    (nestedSeqHOL initializers) (newMainNameHOL declarations) [] entry middle final [] callee
    HolFiniteMapExact.empty calleeShape value limit initRun (by rfl) lookup calleeClock calleeRun calleeShapeMatch calleeBound
  constructor
  · have run := global_lowered_start_return declarations start original returnShape found initializers funs exns context compiled
      pan (PanSemStateFiniteExact.emptyLocalsHOLFinite final) value panCode outerClock wrapperRun outerShapeMatch
    simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using run
  · dsimp only [entry] at wrapperBound
    omega

end SteppedFlapjack.PanToCrepSteps
