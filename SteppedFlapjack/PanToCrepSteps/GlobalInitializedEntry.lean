import SteppedFlapjack.PanToCrepSteps.GlobalFrontendControl
import SteppedFlapjack.PanToCrepSteps.GlobalInitialState
import SteppedFlapjack.PanToCrepSteps.GlobalInitializers
import SteppedFlapjack.PanToCrepSteps.TailEntrySteps
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem initializerBound {width : Nat} [NeZero width] {F : Type}
    (decls : List (DeclHOL width)) (context : PanGlobalsContextExact width)
    (state : PanSemStateFiniteExact width F) :
    controlSteps (nestedSeqHOL (compileDecsExactHOL context decls).1) state ≤ 2 * decls.length + 1 := by
  induction decls generalizing context state with
  | nil => simp [compileDecsExactHOL,controlSteps]
  | cons decl tail ih =>
    cases decl <;> simp only [compileDecsExactHOL,List.length_cons]
    case function => have h := ih context state; omega
    case exnDecl => have h := ih context state; omega
    case name => have h := ih context state; omega
    case decl shape name value =>
      rw [nestedSeqHOL, controlSteps_seq]
      have visit : ∀ addr val, controlSteps (.store addr val : ProgHOL width) state = 1 := by
        intro addr val
        rw [controlSteps.eq_def]
        rfl
      rw [visit]
      generalize run : state.evaluateHOLFiniteState (.store _ _) = result
      rcases result with ⟨out,post⟩
      cases out with
      | none =>
        rw [compileDecsGlobalAddressExact_eq]
        have h := ih {context with globals := context.globals.updateEq (name,shape,context.globalsSize + cakeBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)), globalsSize := context.globalsSize + cakeBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)} post
        simp only
        omega
      | some x => simp only; omega


private theorem entryFromRelation {σ : Type} (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64)
    (init : ProgHOL 64) (name : MlS) (p : ProgHOL 64) (shape : GlobalCallFrontend globals ctxt p)
    (target targetAfter source : PanSemStateFiniteExact 64 σ) (value : BitVec 64)
    (sourceFinal : PanSemStateFiniteExact 64 σ) (sourceLimit initLimit : Nat)
    (initRun : target.evaluateHOLFiniteState init = (none,targetAfter))
    (initBound : controlSteps init target ≤ initLimit)
    (rel : panGlobalsStateRelHOLExact true globals source targetAfter)
    (sourceTable : GlobalCallTable globals (callEntryStateHOLFinite source HolFiniteMapExact.empty).code)
    (found : lookupCodeHOLFinite targetAfter.code.lookup name [] =
      some (compileProgExactHOL globals p,HolFiniteMapExact.empty,.one))
    (clock : targetAfter.clock ≠ 0)
    (run : (callEntryStateHOLFinite source HolFiniteMapExact.empty).evaluateHOLFiniteState p =
      (some (.returned (.val (.word value))),sourceFinal))
    (bound : controlSteps p (callEntryStateHOLFinite source HolFiniteMapExact.empty) ≤ sourceLimit) :
    ∃ targetFinal,
      target.evaluateHOLFiniteState (.seq init (.call none name [])) =
        (some (.returned (.val (.word value))),emptyLocalsHOLFinite targetFinal) ∧
      controlSteps (.seq init (.call none name [])) target ≤ initLimit + sourceLimit + 2 ∧
      sourceFinal.ffi = targetFinal.ffi := by
  have shifted := PanGlobalsStateRelationClock.stateRelDecClockHOL globals source targetAfter true rel
  have entryRel := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL globals source.decClockHOLFinite
    targetAfter.decClockHOLFinite true HolFiniteMapExact.empty).1 shifted
  change panGlobalsStateRelHOLExact true globals (callEntryStateHOLFinite source HolFiniteMapExact.empty)
    (callEntryStateHOLFinite targetAfter HolFiniteMapExact.empty) at entryRel
  obtain ⟨targetFinal,targetRun,finalRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL p
    (callEntryStateHOLFinite source HolFiniteMapExact.empty) (some (.returned (.val (.word value)))) globals
    (callEntryStateHOLFinite targetAfter HolFiniteMapExact.empty) sourceFinal ⟨entryRel,run,by simp⟩
  have visits := globalCallFrontend_controlSteps shape (callEntryStateHOLFinite source HolFiniteMapExact.empty) sourceFinal
    (callEntryStateHOLFinite targetAfter HolFiniteMapExact.empty) (some (.returned (.val (.word value)))) sourceTable run (by simp) entryRel
  have targetBound : controlSteps (compileProgExactHOL globals p) (callEntryStateHOLFinite targetAfter HolFiniteMapExact.empty) ≤ sourceLimit := by
    rw [visits]
    exact bound
  obtain ⟨entryRun,entryBound⟩ := globalEntry_return_with_steps init name [] target targetAfter targetFinal []
    (compileProgExactHOL globals p) HolFiniteMapExact.empty .one (.val (.word value)) sourceLimit
    initRun (by rfl) found clock targetRun (by simp [shapeOfHOLExact,shapeEqHOL]) targetBound
  refine ⟨targetFinal,entryRun,?_,?_⟩
  · change globalEntrySteps init name [] target ≤ _
    omega
  · exact finalRel.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Execute generated global initializers before calling a supported source body,
with a declaration-derived bound on initializer visits. -/
theorem globalInitializedEntry_return {σ : Type} (template : PanSemStateFiniteExact 64 σ)
    (decs : List (DeclHOL 64)) (post : PanSemStateFiniteExact 64 σ)
    (initializers : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
    (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (p : ProgHOL 64) (ctxt : PanToCrepContextExact 64)
    (shape : GlobalCallFrontend globals ctxt p) (value : BitVec 64)
    (sourceFinal : PanSemStateFiniteExact 64 σ) (limit : Nat)
    (structs : template.structs = []) (topFree : ¬ template.memaddrs template.topAddr)
    (aligned : panGlobalsByteAlignedHOL template.topAddr) (clock : template.clock ≠ 0)
    (onlyDecls : ∀ d ∈ decs, isDeclHOL d = true)
    (eval : @evaluateDeclsHOLFinite 64 σ _
      (beforeGlobals (installTargetFunctions template globals entries)
        (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
        ((decShapesHOL decs).map sizeOfShapeHOL).sum) (fun _a => Classical.propDecidable _) decs = some post)
    (compiled : compileDecsExactHOL
      (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)) decs =
        (initializers,funs,exns,globals))
    (allocated : ∀ a, addresses (template.topAddr - panBytesInWord 64 *
      BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      ((decShapesHOL decs).map sizeOfShapeHOL).sum a → template.memaddrs a)
    (sizeBound : (panBytesInWord 64).toNat * ((decShapesHOL decs).map sizeOfShapeHOL).sum < 2 ^ 64)
    (found : entries.lookup name = some ([],p,.one))
    (sourceTable : GlobalCallTable globals
      (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).code)
    (run : (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).evaluateHOLFiniteState p =
      (some (.returned (.val (.word value))),sourceFinal))
    (bound : controlSteps p (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty) ≤ limit) :
    let target := installTargetFunctions template globals entries
    ∃ targetFinal, target.evaluateHOLFiniteState (.seq (nestedSeqHOL initializers) (.call none name [])) =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite targetFinal) ∧
      controlSteps (.seq (nestedSeqHOL initializers) (.call none name [])) target ≤ 2 * decs.length + limit + 3 ∧
      sourceFinal.ffi = targetFinal.ffi := by
  let target := installTargetFunctions template globals entries
  obtain ⟨final,initRun,related,finalClock,finalFfi,finalLocals,finalAlign⟩ :=
    beforeGlobals_initializedFunctions target decs post initializers funs exns globals entries
      structs topFree aligned (by right; rfl) onlyDecls eval compiled allocated sizeBound
  have codeEq := SemInitSupport.eval_code target (nestedSeqHOL initializers)
  rw [initRun] at codeEq
  have id : installTargetFunctions final globals entries = final := by
    have locals : final.locals = (installTargetFunctions template globals entries).locals := finalLocals
    have code : final.code = (installTargetFunctions template globals entries).code := codeEq
    cases final
    simp_all [installTargetFunctions]
  rw [id] at related
  have lookup : lookupCodeHOLFinite final.code.lookup name [] = some (compileProgExactHOL globals p,HolFiniteMapExact.empty,.one) := by
    apply SemInitSupport.lookup_init
    rw [codeEq]
    change FLOOKUP (FUPDATE_LIST FEMPTY (entries.map (fun e => (e.1,e.2.1,compileProgExactHOL globals e.2.2.1,e.2.2.2))).reverse) name = _
    rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup,lookup_mapBodies,found]
    rfl
  have initBound : controlSteps (nestedSeqHOL initializers) target ≤ 2*decs.length+1 := by
    have h := initializerBound decs (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)) target
    rw [compiled] at h
    exact h
  have nonzero : final.clock ≠ 0 := by simpa [target,installTargetFunctions,finalClock] using clock
  have out := entryFromRelation globals ctxt (nestedSeqHOL initializers) name p shape target final
    (installSourceFunctions post entries) value sourceFinal limit (2*decs.length+1)
    initRun initBound related sourceTable lookup nonzero run bound
  obtain ⟨targetFinal,targetRun,targetBound,ffi⟩ := out
  have boundFinal : controlSteps (.seq (nestedSeqHOL initializers) (.call none name [])) target ≤ 2 * decs.length + limit + 3 := by omega
  exact ⟨targetFinal,targetRun,boundFinal,ffi⟩

end SteppedFlapjack.PanToCrepSteps
