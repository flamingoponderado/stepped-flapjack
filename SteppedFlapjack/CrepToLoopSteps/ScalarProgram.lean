import SteppedFlapjack.CrepToLoopSteps.ScalarProgramDef
import SteppedFlapjack.CrepToLoopSteps.FrontendValue
import SteppedFlapjack.CrepToLoopSteps.SimpFixed
import SteppedFlapjack.PanToCrepSteps.FrontendProgram
import Flapjack.Pancake.CrepArith

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.PanToCrepSteps


theorem nestedDecs_scalar {width : Nat} [NeZero width] (names : List Nat)
    (values : List (CrepExpHOL width)) {body : CrepProgHOL width} (h : ScalarProgram body)
    (hs : ∀ value ∈ values, CompiledScalar value) :
    ScalarProgram (nestedDecsHOL names values body) := by
  induction names generalizing values with
  | nil =>
    cases values with
    | nil => exact h
    | cons value values => exact .skip
  | cons name names ih =>
    cases values with
    | nil => exact .skip
    | cons value values =>
      exact .dec _ (hs value (by simp)) (ih values (fun v hv => hs v (by simp [hv])))

theorem nestedStores_scalar {width : Nat} [NeZero width] (address : Nat)
    (names : List Nat) (offset : BitVec width) :
    ScalarProgram (crepNestedSeqHOL (storesHOL (.var address) (names.map CrepExpHOL.var) offset)) := by
  induction names generalizing offset with
  | nil => exact .skip
  | cons name names ih =>
    simp only [List.map_cons,storesHOL,crepNestedSeqHOL]
    apply ScalarProgram.seq
    · apply ScalarProgram.store
      · split
        · exact .direct (.var _)
        · exact .op .add (.direct (.var _)) (.direct (.const _))
      · exact .direct (.var _)
    · exact ih _


theorem frontend_scalar_program {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {p : ProgHOL width}
    (shape : FrontendProgram ctxt p) : ScalarProgram (compileProgExactHOLW ctxt p) := by
  induction shape with
  | skip => simpa [compileProgExactHOLW] using (ScalarProgram.skip : ScalarProgram (.skip : CrepProgHOL width))
  | «break» => simpa [compileProgExactHOLW] using (ScalarProgram.break 0 : ScalarProgram (.break 0 : CrepProgHOL width))
  | «continue» => simpa [compileProgExactHOLW] using (ScalarProgram.continue 0 : ScalarProgram (.continue 0 : CrepProgHOL width))
  | tick => simpa [compileProgExactHOLW] using (ScalarProgram.tick : ScalarProgram (.tick : CrepProgHOL width))
  | @storeValue ctxt a value ha hv =>
    obtain ⟨address,ca,sa⟩ := frontendScalar_compiled ha
    obtain ⟨values,sh,cv,size⟩ := frontendValue_compile hv
    have sv := frontendValue_scalars hv
    rw [cv] at sv
    simp only at sv
    simp only [compileProgExactHOLW,compileStoreExactHOLW,ca,cv,size,
      bne_self_eq_false, Bool.false_eq_true, if_false]
    apply nestedDecs_scalar
    · exact nestedStores_scalar _ _ _
    · intro value member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact sa
      · exact sv value member
  | @store ctxt a v ha hv =>
    obtain ⟨address,ca,sa⟩ := frontendScalar_compiled ha
    obtain ⟨value,cv,sv⟩ := frontendScalar_compiled hv
    simp only [compileProgExactHOLW,compileStoreExactHOLW,ca,cv,sizeOfShapeHOL,
      List.length_cons,List.length_nil,List.range_succ,List.range_zero,nestedDecsHOL]
    exact .dec _ sa (.dec _ sv (.seq (.store (.direct (.var _)) (.direct (.var _))) .skip))
  | @assign ctxt name e reg found he =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    by_cases disjoint : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL value)) = true
    · simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiled,found,disjoint,crepNestedSeqHOL]
      exact .seq (.assign _ scalar) .skip
    · have overlap : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL value)) = false := by
        cases h : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL value)) <;> simp_all
      simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiled,found,overlap,nestedDecsHOL,crepNestedSeqHOL]
      exact .dec _ scalar (.seq (.assign _ (.direct (.var _))) .skip)
  | @declValue ctxt name declared e body he positive hb ih =>
    obtain ⟨values,shape,compiled,size⟩ := frontendValue_compile he
    have each := frontendValue_scalars he
    rw [compiled] at each
    rw [valueDecl_compiled ctxt name declared e body shape values compiled size]
    apply nestedDecs_scalar
    · simpa [compiled] using ih
    · exact each
  | @seq ctxt a b ha hb iha ihb => simpa [compileProgExactHOLW] using ScalarProgram.seq iha ihb
  | @ite ctxt e a b he ha hb iha ihb =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileIfExactHOLW,compiled]
    exact .ite scalar iha ihb
  | @«while» ctxt e body he hb ih =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileWhileExactHOLW,compiled]
    exact .while scalar ih
  | @ret ctxt e he =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileReturnExactHOLW,compiled]
    exact .ret scalar
/-- Crep simplification leaves the recursive scalar fragment unchanged. -/
theorem scalarProgram_simp_fixed {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : ScalarProgram p) : crepSimpProgHOL p = p := by
  induction shape <;> simp_all [crepSimpProgHOL,branchCondition_simp_fixed]

end SteppedFlapjack.CrepToLoopSteps
