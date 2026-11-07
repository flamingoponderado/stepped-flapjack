import SteppedFlapjack.Concrete.FrontendShape
import SteppedFlapjack.CrepSteps.BranchStatic
import SteppedFlapjack.PanToCrepSteps.WhileSteps

/-! Loop-free frontend programs compile to statically bounded Crep programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepSteps

/-- Detect loops within the constructors of the frontend fragment. -/
def noWhile : ProgHOL 64 → Bool
  | .dec _ _ _ body => noWhile body
  | .seq a b => noWhile a && noWhile b
  | .ite _ a b => noWhile a && noWhile b
  | .while _ _ => false
  | _ => true

/-- Loop-free frontend programs, including comparison expressions, compile to
Crep programs whose visits are bounded by their syntax size. -/
theorem frontendLoopFree_static {ctxt : PanToCrepContextExact 64} {p : ProgHOL 64}
    (shape : FrontendProgram ctxt p) (loopFree : noWhile p = true) :
    StaticProgram (compileProgExactHOLW ctxt p) := by
  induction shape with
  | skip => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.skip : CrepProgHOL 64) rfl)
  | «break» => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.break 0 : CrepProgHOL 64) rfl)
  | «continue» => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.continue 0 : CrepProgHOL 64) rfl)
  | tick => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.tick : CrepProgHOL 64) rfl)
  | @store ctxt a v ha hv =>
    obtain ⟨address,ca⟩ := frontendScalar_compile ha
    obtain ⟨value,cv⟩ := frontendScalar_compile hv
    simp only [compileProgExactHOLW,compileStoreExactHOLW,ca,cv,sizeOfShapeHOL,
      List.length_cons,List.length_nil,List.range_succ,List.range_zero,nestedDecsHOL]
    exact .dec _ _ (.dec _ _ (.seq (.leaf _ rfl) (.leaf _ rfl)))
  | @assign ctxt name e reg found he =>
    obtain ⟨value,compiled⟩ := frontendScalar_compile he
    by_cases disjoint : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL value)) = true
    · simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiled,found,disjoint,crepNestedSeqHOL]
      exact .seq (.leaf _ rfl) (.leaf _ rfl)
    · have overlap : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL value)) = false := by
        cases h : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL value)) <;> simp_all
      simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiled,found,overlap,nestedDecsHOL,crepNestedSeqHOL]
      exact .dec _ _ (.seq (.leaf _ rfl) (.leaf _ rfl))
  | @decl ctxt name e body he hb ih =>
    have bodyFree : noWhile body = true := by simpa [noWhile] using loopFree
    obtain ⟨value,compiled⟩ := frontendDecl_compile ctxt name e body he
    rw [compiled]
    exact .dec _ _ (ih bodyFree)
  | @seq ctxt a b ha hb iha ihb =>
    have h : noWhile a = true ∧ noWhile b = true := by simpa [noWhile] using loopFree
    simpa [compileProgExactHOLW] using (StaticProgram.seq (iha h.1) (ihb h.2))
  | @ite ctxt e a b he ha hb iha ihb =>
    have h : noWhile a = true ∧ noWhile b = true := by simpa [noWhile] using loopFree
    obtain ⟨value,compiled⟩ := frontendIf_compile ctxt e a b he
    rw [compiled]
    exact .ite _ (iha h.1) (ihb h.2)
  | «while» => simp [noWhile] at loopFree
  | @ret ctxt e he =>
    obtain ⟨value,compiled⟩ := frontendScalar_compile he
    simp [compileProgExactHOLW,compileReturnExactHOLW,compiled]
    exact .leaf _ rfl

/-- The concrete comparison witness instantiates the generalized static bound. -/
theorem branching_compiled_visits (ctxt : PanToCrepContextExact 64) {σ : Type}
    (state : CrepSemHOLState 64 σ) :
    steps (compileProgExactHOLW ctxt branchingHOL) state ≤
      sizeOf (compileProgExactHOLW ctxt branchingHOL) := by
  apply staticProgram_steps
  apply frontendLoopFree_static (branching_frontend_shape ctxt)
  simp [noWhile,branchingHOL]

/-- A concrete false comparison loop witnesses the generalized while bound. -/
def falseComparisonLoop : ProgHOL 64 :=
  .while (.cmp .lower (.const 1) (.const 0)) .skip

def emptyFrontendContext : PanToCrepContextExact 64 :=
  mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty

def emptyFrontendCrep : CrepSemHOLState 64 Unit := concreteDeclCrepState sourceTemplate []

/-- The comparison-capable while theorem applies to concrete related states. -/
theorem falseComparisonLoop_crep_bound :
    steps (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) emptyFrontendCrep ≤ 2 := by
  have condition : FrontendScalar emptyFrontendContext (.cmp .lower (.const 1) (.const 0)) :=
    .cmp .lower (.const 1) (.const 0)
  have body : StaticProgram (compileProgExactHOLW emptyFrontendContext (.skip : ProgHOL 64)) := by
    simpa [compileProgExactHOLW] using (StaticProgram.leaf (.skip : CrepProgHOL 64) rfl)
  have run : sourceTemplate.evaluateHOLFiniteState falseComparisonLoop = (none,sourceTemplate) := by
    rw [falseComparisonLoop,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have stateRel : panToCrepStateRelFiniteExact sourceTemplate emptyFrontendCrep :=
    concreteDecl_panCrep_stateRel sourceTemplate [] rfl rfl
  have codeRel : codeRelExactHOLW emptyFrontendContext sourceTemplate.code emptyFrontendCrep.code := by
    intro function args program ret found
    simp [sourceTemplate,HolFiniteMapExact.lookup_empty] at found
  have excpRel : panToCrepExcpRelFiniteExact emptyFrontendContext.eids sourceTemplate.eshapes := by
    simpa [emptyFrontendContext,sourceTemplate,mkCtxtExactHOL] using (empty_panCrep_exceptions (width := 64))
  have localsRel : panToCrepLocalsRelFiniteExact emptyFrontendContext sourceTemplate.locals emptyFrontendCrep.locals := by
    apply empty_panCrep_locals
    rfl
  have bound := while_compiled_steps_general (.cmp .lower (.const 1) (.const 0)) .skip
    emptyFrontendContext condition body sourceTemplate sourceTemplate none emptyFrontendCrep
    run (by simp) stateRel codeRel excpRel localsRel (by simp [localisedProgHOL,localisedExpHOL,everyExpHOL])
  have count : controlSteps falseComparisonLoop sourceTemplate = 1 := by
    rw [falseComparisonLoop,controlSteps_while]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  change steps (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) emptyFrontendCrep ≤
    (1 + sizeOf (compileProgExactHOLW emptyFrontendContext (.skip : ProgHOL 64))) *
      controlSteps falseComparisonLoop sourceTemplate at bound
  rw [count] at bound
  simpa [compileProgExactHOLW] using bound

end SteppedFlapjack.Concrete
