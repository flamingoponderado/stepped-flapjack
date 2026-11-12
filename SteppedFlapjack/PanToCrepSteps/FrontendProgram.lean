import SteppedFlapjack.PanToCrepSteps.FrontendValue
import SteppedFlapjack.CrepSteps.BranchStatic

/-! General frontend program shapes and loop-free Crep compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.CrepSteps

/-- The generalized Pancake frontend fragment, tracking the compiler context
through declarations and allowing nested control flow and comparisons. -/
inductive FrontendProgram {width : Nat} [NeZero width] : PanToCrepContextExact width → ProgHOL width → Prop
  | skip {ctxt} : FrontendProgram ctxt .skip
  | break {ctxt} : FrontendProgram ctxt .break
  | continue {ctxt} : FrontendProgram ctxt .continue
  | tick {ctxt} : FrontendProgram ctxt .tick
  | storeStruct {ctxt a fields} : FrontendScalar ctxt a →
      (∀ e ∈ fields, FrontendValue ctxt e) → FrontendProgram ctxt (.store a (.rstruct fields))
  | store {ctxt a v} : FrontendScalar ctxt a → FrontendScalar ctxt v → FrontendProgram ctxt (.store a v)
  | assign {ctxt name e} (reg : Nat) : ctxt.vars.lookup name = some (.one,[reg]) →
      FrontendScalar ctxt e → FrontendProgram ctxt (.assign .local name e)
  | decl {ctxt name e body} : FrontendScalar ctxt e →
      FrontendProgram (scalarDeclContext ctxt name) body → FrontendProgram ctxt (.dec name .one e body)
  | seq {ctxt a b} : FrontendProgram ctxt a → FrontendProgram ctxt b → FrontendProgram ctxt (.seq a b)
  | ite {ctxt e a b} : FrontendScalar ctxt e → FrontendProgram ctxt a → FrontendProgram ctxt b →
      FrontendProgram ctxt (.ite e a b)
  | while {ctxt e body} : FrontendScalar ctxt e → FrontendProgram ctxt body → FrontendProgram ctxt (.while e body)
  | ret {ctxt e} : FrontendScalar ctxt e → FrontendProgram ctxt (.return e)

/-- Frontend programs contain no global-variable references. -/
theorem frontendProgram_localised {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width}
    {p : ProgHOL width} (shape : FrontendProgram ctxt p) : localisedProgHOL p = true := by
  induction shape
  case storeStruct ha hf =>
    rename_i ctxt a fields
    simp only [localisedProgHOL,Bool.and_eq_true]
    refine ⟨frontendScalar_localised ha, ?_⟩
    simp only [localisedExpHOL,everyExpHOL,Bool.true_and]
    induction fields with
    | nil => rfl
    | cons e es ih =>
      simp only [everyExpListHOL,Bool.and_eq_true]
      exact ⟨frontendValue_localised (hf e (by simp)),
        ih (fun x hx => hf x (by simp [hx]))⟩
  all_goals simp_all [localisedProgHOL] <;> aesop (add safe frontendScalar_localised)

/-- The previously established loop-free frontend shape is a subset of the
generalized shape. Its direct-expression guarantees are retained separately. -/
theorem frontendProgram_of_branch {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {program : ProgHOL width}
    (shape : BranchProgram ctxt program) : FrontendProgram ctxt program := by
  induction shape with
  | skip => exact .skip
  | «break» => exact .break
  | «continue» => exact .continue
  | tick => exact .tick
  | «return» e => exact .ret (frontendScalar_of_direct e)
  | assign name reg found e => exact .assign reg found (frontendScalar_of_direct e)
  | store a v => exact .store (frontendScalar_of_direct a) (frontendScalar_of_direct v)
  | seq a b iha ihb => exact .seq iha ihb
  | ite e a b iha ihb => exact .ite (frontendScalar_of_direct e) iha ihb

private theorem nestedDecs_static {width : Nat} [NeZero width] (names : List Nat)
    (values : List (CrepExpHOL width)) {body : CrepProgHOL width} (h : StaticProgram body) :
    StaticProgram (nestedDecsHOL names values body) := by
  induction names generalizing values with
  | nil =>
    cases values with
    | nil => exact h
    | cons value values => exact .leaf _ rfl
  | cons name names ih =>
    cases values with
    | nil => exact .leaf _ rfl
    | cons value values => exact .dec _ _ (ih values)

private theorem nestedStores_static {width : Nat} [NeZero width] (address : CrepExpHOL width)
    (values : List (CrepExpHOL width)) (offset : BitVec width) :
    StaticProgram (crepNestedSeqHOL (storesHOL address values offset)) := by
  induction values generalizing offset with
  | nil => exact .leaf _ rfl
  | cons value values ih =>
    simp only [storesHOL,crepNestedSeqHOL]
    exact .seq (.leaf _ rfl) (ih _)



/-- Detect loops within the constructors of the frontend fragment. -/
def noWhile {width : Nat} [NeZero width] : ProgHOL width → Bool
  | .dec _ _ _ body => noWhile body
  | .seq a b => noWhile a && noWhile b
  | .ite _ a b => noWhile a && noWhile b
  | .while _ _ => false
  | _ => true

/-- Loop-free frontend programs, including comparison expressions, compile to
Crep programs whose visits are bounded by their syntax size. -/
theorem frontendLoopFree_static {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {p : ProgHOL width}
    (shape : FrontendProgram ctxt p) (loopFree : noWhile p = true) :
    StaticProgram (compileProgExactHOLW ctxt p) := by
  induction shape with
  | skip => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.skip : CrepProgHOL width) rfl)
  | «break» => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.break 0 : CrepProgHOL width) rfl)
  | «continue» => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.continue 0 : CrepProgHOL width) rfl)
  | tick => simpa [compileProgExactHOLW] using (StaticProgram.leaf (.tick : CrepProgHOL width) rfl)
  | @storeStruct ctxt a fields ha hf =>
    obtain ⟨address,ca⟩ := frontendScalar_compile ha
    obtain ⟨values,sh,cv,size⟩ := frontendValue_compile (FrontendValue.tuple hf)
    simp only [compileProgExactHOLW,compileStoreExactHOLW,ca,cv,size,
      bne_self_eq_false, Bool.false_eq_true, if_false]
    apply nestedDecs_static
    apply nestedStores_static
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

end SteppedFlapjack.PanToCrepSteps
