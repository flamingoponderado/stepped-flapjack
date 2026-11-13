import SteppedFlapjack.Concrete.ScalarParity
import SteppedFlapjack.CrepSteps.Defs
/-! Compiled supported statements report expression errors with explicit
Crep visit bounds. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

theorem scalar_return_crep_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target)
    (failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = none) :
    evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.return (expToHOL expression))) = (some .error,target) ∧
    CrepSteps.steps (compileProgExactHOLW ctxt (.return (expToHOL expression))) target = 1 := by
  obtain ⟨compiled,compiledEq,failedTarget⟩ := scalar_compile_error scalar ctxt source target locals stateRel failed
  have programEq : compileProgExactHOLW ctxt (.return (expToHOL expression)) = .return [compiled] := by
    simp [compileProgExactHOLW,compileReturnExactHOLW,compiledEq]
  rw [programEq]
  constructor
  · rw [evalCrepSemHOLProgExact_return]
    simp [failedTarget]
  · exact CrepSteps.steps_leaf _ _ rfl
theorem scalar_ite_crep_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target)
    (failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = none) (a b : ProgHOL 64) :
    evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.ite (expToHOL expression) a b)) = (some .error,target) ∧
    CrepSteps.steps (compileProgExactHOLW ctxt (.ite (expToHOL expression) a b)) target = 1 := by
  obtain ⟨compiled,compiledEq,failedTarget⟩ := scalar_compile_error scalar ctxt source target locals stateRel failed
  have programEq : compileProgExactHOLW ctxt (.ite (expToHOL expression) a b) =
      .ite compiled (compileProgExactHOLW ctxt a) (compileProgExactHOLW ctxt b) := by
    simp [compileProgExactHOLW,compileIfExactHOLW,compiledEq]
  rw [programEq]
  constructor
  · rw [evalCrepSemHOLProgExact_ite_holShape,failedTarget]
  · rw [CrepSteps.steps_ite,failedTarget]
    rfl

theorem scalar_while_crep_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target)
    (failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = none) (body : ProgHOL 64) :
    evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.while (expToHOL expression) body)) = (some .error,target) ∧
    CrepSteps.steps (compileProgExactHOLW ctxt (.while (expToHOL expression) body)) target = 1 := by
  obtain ⟨compiled,compiledEq,failedTarget⟩ := scalar_compile_error scalar ctxt source target locals stateRel failed
  have programEq : compileProgExactHOLW ctxt (.while (expToHOL expression) body) =
      .while compiled (compileProgExactHOLW ctxt body) := by
    simp [compileProgExactHOLW,compileWhileExactHOLW,compiledEq]
  rw [programEq]
  constructor
  · rw [evalCrepSemHOLProgExact_while_holShape,failedTarget]
  · rw [CrepSteps.steps_while,failedTarget]
    rfl

theorem scalar_decl_crep_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target)
    (failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = none) (name : Flapjack.Basis.Pure.MlString.MlString) (body : ProgHOL 64) :
    evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.dec name .one (expToHOL expression) body)) = (some .error,target) ∧
    CrepSteps.steps (compileProgExactHOLW ctxt (.dec name .one (expToHOL expression) body)) target = 1 := by
  obtain ⟨compiled,compiledEq,failedTarget⟩ := scalar_compile_error scalar ctxt source target locals stateRel failed
  have programEq : compileProgExactHOLW ctxt (.dec name .one (expToHOL expression) body) =
      .dec (ctxt.vmax+1) compiled (compileProgExactHOLW (scalarDeclContext ctxt name) body) := by
    simp [compileProgExactHOLW,compileDecExactHOLW,compiledEq,nestedDecsHOL,scalarDeclContext]
  rw [programEq]
  constructor
  · rw [evalCrepSemHOLProgExact_dec_holShape,failedTarget]
  · rw [CrepSteps.steps_dec,failedTarget]
    rfl
theorem scalar_assign_crep_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target)
    (failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = none) (name : VarName) (member : name ∈ scope) :
    evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.assign .local (Flapjack.Basis.Pure.MlString.ofString name) (expToHOL expression))) = (some .error,target) ∧
    CrepSteps.steps (compileProgExactHOLW ctxt (.assign .local (Flapjack.Basis.Pure.MlString.ofString name) (expToHOL expression))) target ≤ 2 := by
  obtain ⟨compiled,compiledEq,failedTarget⟩ := scalar_compile_error scalar ctxt source target locals stateRel failed
  obtain ⟨reg,found,_⟩ := locals name member
  by_cases disjoint : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL compiled)) = true
  · have programEq : compileProgExactHOLW ctxt (.assign .local (Flapjack.Basis.Pure.MlString.ofString name) (expToHOL expression)) =
        .seq (.assign reg compiled) .skip := by
      simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiledEq,found,disjoint,crepNestedSeqHOL]
    rw [programEq]
    have assignRun : evalCrepSemHOLProgExact target (.assign reg compiled) = (some .error,target) := by
      rw [evalCrepSemHOLProgExact_assign_holShape,failedTarget]
    constructor
    · simp [evalCrepSemHOLProgExact_seq_holShape,assignRun]
    · rw [CrepSteps.steps_seq,assignRun]
      have one : CrepSteps.steps (.assign reg compiled) target = 1 := CrepSteps.steps_leaf _ _ rfl
      simp [one]
  · have overlap : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL compiled)) = false := Bool.eq_false_iff.mpr disjoint
    have programEq : compileProgExactHOLW ctxt (.assign .local (Flapjack.Basis.Pure.MlString.ofString name) (expToHOL expression)) =
        .dec (ctxt.vmax+1) compiled (.seq (.assign reg (.var (ctxt.vmax+1))) .skip) := by
      simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiledEq,found,overlap,nestedDecsHOL,crepNestedSeqHOL]
    rw [programEq]
    constructor
    · rw [evalCrepSemHOLProgExact_dec_holShape,failedTarget]
    · rw [CrepSteps.steps_dec,failedTarget]
      simp
/-- Assigning to an absent local reports an error in either generated
assignment layout, with at most three Crep visits. -/
theorem scalar_assign_absent_crep_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target) (maxBound : ctxtMaxFiniteExact ctxt.vmax ctxt.vars)
    (name : VarName) (member : name ∈ scope) (absent : source.locals.lookup (ofString name) = none) :
    ∃ final, evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.assign .local (ofString name) (expToHOL expression))) = (some .error,final) ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (.assign .local (ofString name) (expToHOL expression))) target ≤ 3 := by
  obtain ⟨compiled,compiledEq,_⟩ := scalar_compile_eval_all scalar ctxt source target locals stateRel
  obtain ⟨reg,found,agreement⟩ := locals name member
  have missing : target.locals.lookup reg = none := by
    rw [absent] at agreement
    cases h : target.locals.lookup reg with
    | none => rfl
    | some value => simp [h] at agreement
  by_cases disjoint : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL compiled)) = true
  · have programEq : compileProgExactHOLW ctxt (.assign .local (ofString name) (expToHOL expression)) =
        .seq (.assign reg compiled) .skip := by
      simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiledEq,found,disjoint,crepNestedSeqHOL]
    rw [programEq]
    have assignRun : evalCrepSemHOLProgExact target (.assign reg compiled) = (some .error,target) := by
      rw [evalCrepSemHOLProgExact_assign_holShape]
      cases h : evalCrepSemHOLExp target compiled <;> simp [missing]
    refine ⟨target,?_,?_⟩
    · simp [evalCrepSemHOLProgExact_seq_holShape,assignRun]
    · rw [CrepSteps.steps_seq,assignRun]
      have one : CrepSteps.steps (.assign reg compiled) target = 1 := CrepSteps.steps_leaf _ _ rfl
      simp [one]
  · have overlap : distinctListsHol [reg] (crepExpVarsW (crepExpOfHOL compiled)) = false := Bool.eq_false_iff.mpr disjoint
    have programEq : compileProgExactHOLW ctxt (.assign .local (ofString name) (expToHOL expression)) =
        .dec (ctxt.vmax+1) compiled (.seq (.assign reg (.var (ctxt.vmax+1))) .skip) := by
      simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiledEq,found,overlap,nestedDecsHOL,crepNestedSeqHOL]
    rw [programEq]
    have regBound : reg ≤ ctxt.vmax := maxBound.2 _ _ _ found reg (by simp)
    have fresh : reg ≠ ctxt.vmax+1 := by omega
    cases h : evalCrepSemHOLExp target compiled with
    | none =>
      refine ⟨target,?_,?_⟩
      · rw [evalCrepSemHOLProgExact_dec_holShape,h]
      · rw [CrepSteps.steps_dec,h]
        simp
    | some word =>
      let entered := {target with locals := target.locals.updateEq (ctxt.vmax+1,word)}
      have missingEntry : entered.locals.lookup reg = none := by
        simp [entered,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,fresh,missing]
      have assignRun : evalCrepSemHOLProgExact entered (.assign reg (.var (ctxt.vmax+1))) = (some .error,entered) := by
        have tmpVal : entered.locals.lookup (ctxt.vmax+1) = some word := by
          simp [entered,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]
        rw [evalCrepSemHOLProgExact_assign_holShape]
        simp [evalCrepSemHOLExp,tmpVal,missingEntry]
      let final := {entered with locals := entered.locals.resVarEq (ctxt.vmax+1,target.locals.lookup (ctxt.vmax+1))}
      refine ⟨final,?_,?_⟩
      · rw [evalCrepSemHOLProgExact_dec_holShape,h]
        change (match evalCrepSemHOLProgExact entered (.seq (.assign reg (.var (ctxt.vmax+1))) .skip) with
          | (res,st) => (res,{st with locals := st.locals.resVarEq (ctxt.vmax+1,target.locals.lookup (ctxt.vmax+1))})) = _
        simp [evalCrepSemHOLProgExact_seq_holShape,assignRun,final]
      · rw [CrepSteps.steps_dec,h]
        change 1 + CrepSteps.steps (.seq (.assign reg (.var (ctxt.vmax+1))) .skip) entered ≤ 3
        rw [CrepSteps.steps_seq,assignRun]
        have one : CrepSteps.steps (.assign reg (.var (ctxt.vmax+1))) entered = 1 := CrepSteps.steps_leaf _ _ rfl
        simp [one]
/-- Every supported local-assignment error reaches a Crep error in at most
three visits, whether its expression fails or its destination is absent. -/
theorem scalar_assign_hol_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target) (maxBound : ctxtMaxFiniteExact ctxt.vmax ctxt.vars)
    (name : VarName) (member : name ∈ scope)
    (run : source.evaluateHOLFiniteState (.assign .local (ofString name) (expToHOL expression)) = (some .error,source)) :
    ∃ final, evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.assign .local (ofString name) (expToHOL expression))) = (some .error,final) ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (.assign .local (ofString name) (expToHOL expression))) target ≤ 3 := by
  obtain ⟨compiled,_,evalEq⟩ := scalar_compile_eval_all scalar ctxt source target locals stateRel
  cases h : evalCrepSemHOLExp target compiled with
  | none =>
    have failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) = none := by
      rw [evalEq,h]
      rfl
    obtain ⟨targetRun,bound⟩ := scalar_assign_crep_error scalar ctxt source target locals stateRel failed name member
    exact ⟨target,targetRun,by omega⟩
  | some value =>
    cases value with
    | word word =>
      have sourceEval : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
          (expToHOL expression) = some (.val (.word word)) := by rw [evalEq,h]; rfl
      obtain ⟨reg,found,agreement⟩ := locals name member
      have absent : source.locals.lookup (ofString name) = none := by
        cases old : target.locals.lookup reg with
        | none => simpa [old] using agreement
        | some v =>
          cases v with
          | word oldWord =>
            have sourceOld : source.locals.lookup (ofString name) = some (.val (.word oldWord)) := by
              simpa [old] using agreement
            rw [evaluateHOLFiniteState_assign,sourceEval] at run
            simp [isValidValueHOLExact,lookupKvarHOLExact,sourceOld,shapeOfHOLExact,shapeEqHOL] at run
      exact scalar_assign_absent_crep_error scalar ctxt source target locals stateRel maxBound name member absent
/-- Every supported scalar return error reaches a Crep error in one visit. -/
theorem scalar_return_hol_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target) (stateRel : panToCrepStateRelFiniteExact source target)
    (run : source.evaluateHOLFiniteState (.return (expToHOL expression)) = (some .error,source)) :
    evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.return (expToHOL expression))) = (some .error,target) ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (.return (expToHOL expression))) target = 1 := by
  obtain ⟨compiled,_,evalEq⟩ := scalar_compile_eval_all scalar ctxt source target locals stateRel
  cases h : evalCrepSemHOLExp target compiled with
  | none =>
    have failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) = none := by
      rw [evalEq,h]
      rfl
    exact scalar_return_crep_error scalar ctxt source target locals stateRel failed
  | some value =>
    cases value with
    | word word =>
      have sourceEval : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
          (expToHOL expression) = some (.val (.word word)) := by rw [evalEq,h]; rfl
      rw [evaluateHOLFiniteState_return,sourceEval] at run
      simp [shapeOfHOLExact] at run
end SteppedFlapjack.Concrete
