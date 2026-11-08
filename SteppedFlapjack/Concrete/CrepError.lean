import SteppedFlapjack.Concrete.ScopePreservation
import SteppedFlapjack.Concrete.CrepErrorLeaf
import SteppedFlapjack.PanToCrepSteps.WhileSteps
/-! Error preservation and a code-derived visit bound for supported compilation. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

private theorem normal_bridge {σ : Type} {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (ctxt : PanToCrepContextExact 64)
    (source middle : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (registered : ScopeRelation scope ctxt) (present : ScalarScopePresent scope source)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (run : source.evaluateHOLFiniteState (progToHOL program) = (none,middle)) :
    ∃ targetMiddle,
      evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (progToHOL program)) = (none,targetMiddle) ∧
      panToCrepStateRelFiniteExact middle targetMiddle ∧
      codeRelExactHOLW ctxt middle.code targetMiddle.code ∧
      panToCrepExcpRelFiniteExact ctxt.eids middle.eshapes ∧
      panToCrepLocalsRelFiniteExact ctxt middle.locals targetMiddle.locals ∧
      ScalarScopePresent scope middle ∧
      ScalarLocalsRel scope ctxt middle targetMiddle ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (progToHOL program)) target ≤
        CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL program)) * controlSteps (progToHOL program) source := by
  have shape := supportedIn_frontend_shape supported ctxt registered
  obtain ⟨res,after,runTarget,finalRel,finalCode,finalExcp,resultRel,bound⟩ :=
    frontend_correct_with_steps ctxt (progToHOL program) shape source middle none target _
      run (by simp) (by rfl) stateRel codeRel excpRel localsRel
  have ⟨resEq,finalLocals⟩ := resultRel
  subst res
  have finalPresent := supported_scope_result supported source middle none present run
  exact ⟨after,runTarget,finalRel,finalCode,finalExcp,finalLocals,finalPresent,
    ScalarLocalsRel.of_existing registered finalPresent finalLocals,bound⟩

private def ErrorBridge (scope : List VarName) (program : Prog (RiscV.Word 64)) : Prop :=
 ∀ {σ : Type} (ctxt : PanToCrepContextExact 64) (source sourceFinal : PanSemStateFiniteExact 64 σ)
   (target : CrepSemHOLState 64 σ), ScopeRelation scope ctxt → ScalarScopePresent scope source →
   panToCrepStateRelFiniteExact source target → codeRelExactHOLW ctxt source.code target.code →
   panToCrepExcpRelFiniteExact ctxt.eids source.eshapes →
   panToCrepLocalsRelFiniteExact ctxt source.locals target.locals →
   source.evaluateHOLFiniteState (progToHOL program) = (some .error,sourceFinal) →
   ∃ targetFinal, evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (progToHOL program)) = (some .error,targetFinal) ∧
     CrepSteps.steps (compileProgExactHOLW ctxt (progToHOL program)) target ≤
       3 * CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL program)) * controlSteps (progToHOL program) source

private theorem errorSkip {scope : List VarName} : ErrorBridge scope .skip := by
 intro σ ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
 simp [progToHOL,evaluateHOLFiniteState_skip] at run

private theorem errorReturn {scope : List VarName} {expression : Exp (RiscV.Word 64)}
 (scalar : Scalar scope expression) : ErrorBridge scope (.return expression) := by
 intro σ ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
 have rel := ScalarLocalsRel.of_existing registered present localsRel
 have sourceSame : sourceFinal = source := by
  simp only [progToHOL,evaluateHOLFiniteState_return] at run
  split at run
  · exact (Prod.mk.inj run).2.symm
  · split at run <;> simp_all
 subst sourceFinal
 have pair := scalar_return_hol_error scalar ctxt source target rel (by simpa [progToHOL] using run)
 refine ⟨target,?_,?_⟩
 · simpa [progToHOL] using pair.1
 · rw [show progToHOL (.return expression) = .return (expToHOL expression) from by simp [progToHOL]]
   rw [pair.2]
   have count : controlSteps (.return (expToHOL expression)) source = 1 := by rw [controlSteps.eq_def]; rfl
   rw [count]
   have positive : 0 < CrepSteps.statementWeight (compileProgExactHOLW ctxt (.return (expToHOL expression))) := by
     exact CrepSteps.statementWeight_pos _
   omega

private theorem errorAssign {scope : List VarName} (name : VarName) (member : name ∈ scope)
 {expression : Exp (RiscV.Word 64)} (scalar : Scalar scope expression) : ErrorBridge scope (.assign .local name expression) := by
 intro σ ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
 have rel := ScalarLocalsRel.of_existing registered present localsRel
 have maxBound : ctxtMaxFiniteExact ctxt.vmax ctxt.vars := localsRel.2.1
 have sourceSame : sourceFinal = source := by
  simp only [progToHOL,evaluateHOLFiniteState_assign] at run
  split at run
  · exact (Prod.mk.inj run).2.symm
  · split at run <;> simp_all
 subst sourceFinal
 obtain ⟨after,targetRun,bound⟩ := scalar_assign_hol_error scalar ctxt source target rel maxBound name member (by simpa [progToHOL] using run)
 refine ⟨after,?_,?_⟩
 · simpa [progToHOL] using targetRun
 · rw [show progToHOL (.assign .local name expression) = .assign .local (ofString name) (expToHOL expression) from by simp [progToHOL]]
   have count : controlSteps (.assign .local (ofString name) (expToHOL expression)) source = 1 := by rw [controlSteps.eq_def]; rfl
   rw [count]
   have positive : 0 < CrepSteps.statementWeight (compileProgExactHOLW ctxt (.assign .local (ofString name) (expToHOL expression))) := by
     exact CrepSteps.statementWeight_pos _
   omega

private theorem errorSeq {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (aSupported : SupportedIn scope a) (aError : ErrorBridge scope a) (bError : ErrorBridge scope b) : ErrorBridge scope (.seq a b) := by
 intro σ ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
 simp only [progToHOL,evaluateHOLFiniteState_seq_line780] at run
 rcases firstRun : source.evaluateHOLFiniteState (progToHOL a) with ⟨firstResult,middle⟩
 rw [firstRun] at run
 have sourceCount := controlSteps_seq (progToHOL a) (progToHOL b) source
 rw [firstRun] at sourceCount
 have leftSize : CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL a)) ≤
     CrepSteps.statementWeight (compileProgExactHOLW ctxt (.seq (progToHOL a) (progToHOL b))) := by
   simp only [compileProgExactHOLW]
   simp only [CrepSteps.statementWeight]
   omega
 have rightSize : CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL b)) ≤
     CrepSteps.statementWeight (compileProgExactHOLW ctxt (.seq (progToHOL a) (progToHOL b))) := by
   simp only [compileProgExactHOLW]
   simp only [CrepSteps.statementWeight]
   omega
 simp only [compileProgExactHOLW] at leftSize rightSize
 have parentPositive : 0 < CrepSteps.statementWeight (.seq (compileProgExactHOLW ctxt (progToHOL a)) (compileProgExactHOLW ctxt (progToHOL b)) : CrepProgHOL 64) := by simp only [CrepSteps.statementWeight]; omega
 cases firstResult with
 | none =>
   obtain ⟨targetMiddle,firstTarget,midState,midCode,midExcp,midLocals,midPresent,_,firstBound⟩ :=
     normal_bridge aSupported ctxt source middle target registered present stateRel codeRel excpRel localsRel firstRun
   obtain ⟨after,secondTarget,secondBound⟩ := bError ctxt middle sourceFinal targetMiddle registered midPresent midState midCode midExcp midLocals run
   refine ⟨after,?_,?_⟩
   · simp only [progToHOL,compileProgExactHOLW,evalCrepSemHOLProgExact_seq_holShape,firstTarget]
     exact secondTarget
   · simp only [progToHOL,compileProgExactHOLW,CrepSteps.steps_seq,firstTarget,sourceCount]
     nlinarith [Nat.mul_le_mul_right (controlSteps (progToHOL a) source) leftSize, Nat.mul_le_mul_right (controlSteps (progToHOL b) middle) rightSize]
 | some result =>
   have firstErr : result = .error := by exact Option.some.inj (Prod.mk.inj run).1
   subst result
   have finalEq : middle = sourceFinal := (Prod.mk.inj run).2
   subst sourceFinal
   obtain ⟨after,firstTarget,firstBound⟩ := aError ctxt source middle target registered present stateRel codeRel excpRel localsRel firstRun
   refine ⟨after,?_,?_⟩
   · simp [progToHOL,compileProgExactHOLW,evalCrepSemHOLProgExact_seq_holShape,firstTarget]
   · simp only [progToHOL,compileProgExactHOLW,CrepSteps.steps_seq,firstTarget,sourceCount]
     nlinarith [Nat.mul_le_mul_right (controlSteps (progToHOL a) source) leftSize]

private theorem errorIte {scope : List VarName} {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
 (scalar : Scalar scope condition) (aError : ErrorBridge scope a) (bError : ErrorBridge scope b) : ErrorBridge scope (.ite condition a b) := by
 intro σ ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
 have rel := ScalarLocalsRel.of_existing registered present localsRel
 obtain ⟨ce,compiled,evalEq⟩ := scalar_compile_eval_all scalar ctxt source target rel
 have comp : compileProgExactHOLW ctxt (.ite (expToHOL condition) (progToHOL a) (progToHOL b)) =
   .ite ce (compileProgExactHOLW ctxt (progToHOL a)) (compileProgExactHOLW ctxt (progToHOL b)) := by
  simp [compileProgExactHOLW,compileIfExactHOLW,compiled]
 have sourceCount := controlSteps_ite (expToHOL condition) (progToHOL a) (progToHOL b) source
 cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun v => Classical.propDecidable (source.memaddrs v)) (expToHOL condition) with
 | none =>
   obtain ⟨targetRun,bound⟩ := scalar_ite_crep_error scalar ctxt source target rel evaluated (progToHOL a) (progToHOL b)
   refine ⟨target,?_,?_⟩
   · simpa [progToHOL] using targetRun
   · simp only [progToHOL,bound,sourceCount,evaluated]
     rw [comp]
     simp only [CrepSteps.statementWeight]
     omega
 | some value =>
   obtain ⟨word,rfl⟩ := scalar_hol_word scalar source present value evaluated
   have targetEval : evalCrepSemHOLExp target ce = some (.word word) := by
     rw [evalEq] at evaluated
     cases h : evalCrepSemHOLExp target ce with
     | none => simp [h] at evaluated
     | some value => cases value with | word w => simp [h] at evaluated; subst w; rfl
   simp only [progToHOL,evaluateHOLFiniteState_ite,evaluated] at run
   simp only [evaluated] at sourceCount
   have leftSize : CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL a)) ≤ CrepSteps.statementWeight (compileProgExactHOLW ctxt (.ite (expToHOL condition) (progToHOL a) (progToHOL b))) := by rw [comp]; simp only [CrepSteps.statementWeight]; omega
   have rightSize : CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL b)) ≤ CrepSteps.statementWeight (compileProgExactHOLW ctxt (.ite (expToHOL condition) (progToHOL a) (progToHOL b))) := by rw [comp]; simp only [CrepSteps.statementWeight]; omega
   by_cases zero : word = 0
   · simp only [zero] at run
     obtain ⟨after,targetRun,bound⟩ := bError ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
     refine ⟨after,?_,?_⟩
     · simp only [progToHOL,comp,evalCrepSemHOLProgExact_ite_holShape,targetEval,zero]
       exact targetRun
     · simp only [progToHOL,comp,CrepSteps.steps_ite,targetEval,zero,ne_eq,not_true_eq_false,if_false,sourceCount]
       rw [comp] at rightSize
       have pos : 0 < CrepSteps.statementWeight (.ite ce (compileProgExactHOLW ctxt (progToHOL a)) (compileProgExactHOLW ctxt (progToHOL b)) : CrepProgHOL 64) := by simp only [CrepSteps.statementWeight]; omega
       nlinarith [Nat.mul_le_mul_right (controlSteps (progToHOL b) source) rightSize]
   · simp only [if_neg zero] at run
     obtain ⟨after,targetRun,bound⟩ := aError ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
     refine ⟨after,?_,?_⟩
     · simp only [progToHOL,comp,evalCrepSemHOLProgExact_ite_holShape,targetEval,if_pos zero]
       exact targetRun
     · simp only [progToHOL,comp,CrepSteps.steps_ite,targetEval,if_pos zero,sourceCount]
       rw [comp] at leftSize
       have pos : 0 < CrepSteps.statementWeight (.ite ce (compileProgExactHOLW ctxt (progToHOL a)) (compileProgExactHOLW ctxt (progToHOL b)) : CrepProgHOL 64) := by simp only [CrepSteps.statementWeight]; omega
       nlinarith [Nat.mul_le_mul_right (controlSteps (progToHOL a) source) leftSize]

private theorem errorDecl {scope : List VarName} (name : VarName) {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
 (scalar : Scalar scope initializer) (bodyError : ErrorBridge (name :: scope) body) : ErrorBridge scope (.dec name .one initializer body) := by
 intro σ ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
 have rel := ScalarLocalsRel.of_existing registered present localsRel
 obtain ⟨ce,compiled,evalEq⟩ := scalar_compile_eval_all scalar ctxt source target rel
 have comp : compileProgExactHOLW ctxt (.dec (ofString name) .one (expToHOL initializer) (progToHOL body)) =
   .dec (ctxt.vmax+1) ce (compileProgExactHOLW (scalarDeclContext ctxt (ofString name)) (progToHOL body)) := by
  simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext]
 cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun v => Classical.propDecidable (source.memaddrs v)) (expToHOL initializer) with
 | none =>
   obtain ⟨targetRun,bound⟩ := scalar_decl_crep_error scalar ctxt source target rel evaluated (ofString name) (progToHOL body)
   refine ⟨target,?_,?_⟩
   · simpa [progToHOL,shapeToHOL] using targetRun
   · simp only [progToHOL,shapeToHOL,bound]
     have count : controlSteps (.dec (ofString name) .one (expToHOL initializer) (progToHOL body)) source = 1 := by rw [controlSteps.eq_def]; simp [evaluated]
     rw [count,comp]
     simp only [CrepSteps.statementWeight]
     omega
 | some value =>
   obtain ⟨word,rfl⟩ := scalar_hol_word scalar source present value evaluated
   have targetEval : evalCrepSemHOLExp target ce = some (.word word) := by
     rw [evalEq] at evaluated
     cases h : evalCrepSemHOLExp target ce with
     | none => simp [h] at evaluated
     | some value => cases value with | word w => simp [h] at evaluated; subst w; rfl
   simp only [progToHOL,shapeToHOL,evaluateHOLFiniteState_dec_total,evaluated] at run
   have valid : shapeEqHOL .one (shapeOfHOLExact (.val (.word word))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
   rw [if_pos valid] at run
   rcases bodyRun : (setVarHOLFinite (ofString name) (.val (.word word)) source).evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,bodyFinal⟩
   rw [bodyRun] at run
   have resultEq : bodyResult = some .error := (Prod.mk.inj run).1
   subst bodyResult
   have innerLocals := localsRelExtendNewVarHOL ctxt source.locals target.locals
      (.val (.word word)) (ofString name) [ctxt.vmax+1] (by refine ⟨localsRel, ?_, ?_, ?_, ?_⟩ <;> simp [shapeOfHOLExact])
   have innerState : panToCrepStateRelFiniteExact
      (setVarHOLFinite (ofString name) (.val (.word word)) source)
      (CrepSemHOLState.setVar (ctxt.vmax+1) (.word word) target) := by
     simpa [panToCrepStateRelFiniteExact,setVarHOLFinite,CrepSemHOLState.setVar] using stateRel
   have singletonUpdate : target.locals.updateListEq [(ctxt.vmax+1,.word word)] = target.locals.updateEq (ctxt.vmax+1,.word word) := by
     apply HolFiniteMapExact.ext
     funext k
     rfl
   have innerLocalsRel : panToCrepLocalsRelFiniteExact (scalarDeclContext ctxt (ofString name))
      (setVarHOLFinite (ofString name) (.val (.word word)) source).locals
      (CrepSemHOLState.setVar (ctxt.vmax+1) (.word word) target).locals := by
     simpa [scalarDeclContext,setVarHOLFinite,CrepSemHOLState.setVar,shapeOfHOLExact,
       Flapjack.Pancake.PanLang.sizeOfShapeHOL,flattenHOL,singletonUpdate] using innerLocals
   have innerCode : codeRelExactHOLW (scalarDeclContext ctxt (ofString name))
      (setVarHOLFinite (ofString name) (.val (.word word)) source).code
      (CrepSemHOLState.setVar (ctxt.vmax+1) (.word word) target).code := by
     simpa [codeRelExactHOLW,scalarDeclContext,setVarHOLFinite,CrepSemHOLState.setVar] using codeRel
   have innerExcp : panToCrepExcpRelFiniteExact (scalarDeclContext ctxt (ofString name)).eids
      (setVarHOLFinite (ofString name) (.val (.word word)) source).eshapes := by
     simpa [scalarDeclContext,setVarHOLFinite] using excpRel
   obtain ⟨after,targetRun,bound⟩ := bodyError (scalarDeclContext ctxt (ofString name))
      (setVarHOLFinite (ofString name) (.val (.word word)) source) bodyFinal
      (CrepSemHOLState.setVar (ctxt.vmax+1) (.word word) target)
      (registered.declare name) (present.setVar name word) innerState innerCode innerExcp innerLocalsRel bodyRun
   let final := {after with locals := after.locals.resVarEq (ctxt.vmax+1,target.locals.lookup (ctxt.vmax+1))}
   refine ⟨final,?_,?_⟩
   · simp only [progToHOL,shapeToHOL,comp,evalCrepSemHOLProgExact_dec_holShape,targetEval]
     change (match evalCrepSemHOLProgExact (CrepSemHOLState.setVar (ctxt.vmax+1) (.word word) target) _ with
       | (res,st) => (res,{st with locals := st.locals.resVarEq (ctxt.vmax+1,target.locals.lookup (ctxt.vmax+1))})) = _
     rw [targetRun]
   · have count := controlSteps_dec (ofString name) .one (expToHOL initializer) (progToHOL body) source (.val (.word word)) evaluated valid
     simp only [progToHOL,shapeToHOL,comp,CrepSteps.steps_dec,targetEval,count]
     have childSize : CrepSteps.statementWeight (compileProgExactHOLW (scalarDeclContext ctxt (ofString name)) (progToHOL body)) ≤
        CrepSteps.statementWeight (.dec (ctxt.vmax+1) ce (compileProgExactHOLW (scalarDeclContext ctxt (ofString name)) (progToHOL body)) : CrepProgHOL 64) := by simp only [CrepSteps.statementWeight]; omega
     have pos : 0 < CrepSteps.statementWeight (.dec (ctxt.vmax+1) ce (compileProgExactHOLW (scalarDeclContext ctxt (ofString name)) (progToHOL body)) : CrepProgHOL 64) := by simp only [CrepSteps.statementWeight]; omega
     nlinarith [Nat.mul_le_mul_right (controlSteps (progToHOL body) (setVarHOLFinite (ofString name) (.val (.word word)) source)) childSize]

private theorem errorWhile {scope : List VarName} {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
 (scalar : Scalar scope condition) (bodySupported : SupportedIn scope body) (bodyError : ErrorBridge scope body) : ErrorBridge scope (.while condition body) := by
 intro σ ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
 simp only [progToHOL] at run ⊢
 induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal target with
 | _ clock ih =>
  have rel := ScalarLocalsRel.of_existing registered present localsRel
  obtain ⟨ce,compiled,evalEq⟩ := scalar_compile_eval_all scalar ctxt source target rel
  have comp : compileProgExactHOLW ctxt (.while (expToHOL condition) (progToHOL body)) =
    .while ce (compileProgExactHOLW ctxt (progToHOL body)) := by
    simp [compileProgExactHOLW,compileWhileExactHOLW,compiled]
  have sourceCount := controlSteps_while (expToHOL condition) (progToHOL body) source
  cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun v => Classical.propDecidable (source.memaddrs v)) (expToHOL condition) with
  | none =>
    obtain ⟨targetRun,bound⟩ := scalar_while_crep_error scalar ctxt source target rel evaluated (progToHOL body)
    refine ⟨target,targetRun,?_⟩
    simp only [bound,sourceCount,evaluated]
    rw [comp]
    simp only [CrepSteps.statementWeight]
    omega
  | some value =>
    obtain ⟨word,rfl⟩ := scalar_hol_word scalar source present value evaluated
    have targetEval : evalCrepSemHOLExp target ce = some (.word word) := by
      rw [evalEq] at evaluated
      cases h : evalCrepSemHOLExp target ce with
      | none => simp [h] at evaluated
      | some value => cases value with | word w => simp [h] at evaluated; subst w; rfl
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at run
    simp only [evalHOLFinite,evaluated] at run
    simp only [evaluated] at sourceCount
    by_cases zero : word = 0
    · simp [zero] at run
    · have zeroBits : word ≠ (0#64) := by simpa using zero
      by_cases noClock : source.clock = 0
      · simp [zeroBits,noClock] at run
      · simp only [if_pos zero,if_neg noClock] at run
        have clockRel : source.clock = target.clock := stateRel.2.2.2.2.2.1
        have targetClock : target.clock ≠ 0 := clockRel ▸ noClock
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,sourcePost⟩
        rw [bodyRun] at run
        have bodyState : panToCrepStateRelFiniteExact source.decClockHOLFinite (decClockCrepSemHOL target) := by
          simpa [panToCrepStateRelFiniteExact,decClockHOLFinite,decClockCrepSemHOL,clockRel] using stateRel
        have entryPresent : ScalarScopePresent scope source.decClockHOLFinite := by simpa [ScalarScopePresent,decClockHOLFinite] using present
        have bodyScope := supported_scope_result bodySupported source.decClockHOLFinite sourcePost bodyResult entryPresent bodyRun
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by simp only [decClockHOLFinite] at bodyClock; omega
        simp only [if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨zero,noClock⟩),bodyRun] at sourceCount
        have childSize : CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL body)) ≤ CrepSteps.statementWeight (.while ce (compileProgExactHOLW ctxt (progToHOL body)) : CrepProgHOL 64) := by simp only [CrepSteps.statementWeight]; omega
        have pos : 0 < CrepSteps.statementWeight (.while ce (compileProgExactHOLW ctxt (progToHOL body)) : CrepProgHOL 64) := by simp only [CrepSteps.statementWeight]; omega
        cases bodyResult with
        | none =>
          obtain ⟨targetPost,targetBody,postState,postCode,postExcp,postLocals,postPresent,_,bodyBound⟩ :=
            normal_bridge bodySupported ctxt source.decClockHOLFinite sourcePost (decClockCrepSemHOL target)
              registered entryPresent bodyState codeRel excpRel localsRel bodyRun
          obtain ⟨after,targetTail,tailBound⟩ := ih sourcePost.clock smaller sourcePost sourceFinal targetPost
            postPresent postState postCode postExcp postLocals (by simpa using run) rfl
          rw [comp] at targetTail tailBound
          refine ⟨after,?_,?_⟩
          · rw [comp,evalCrepSemHOLProgExact_while_holShape,targetEval]
            simp only [if_pos zero,if_neg targetClock,targetBody]
            exact targetTail
          · rw [comp,CrepSteps.steps_while,targetEval]
            simp only [if_pos (show word ≠ 0 ∧ target.clock ≠ 0 from ⟨zero,targetClock⟩),targetBody]
            simp only [sourceCount]
            nlinarith [Nat.mul_le_mul_right (controlSteps (progToHOL body) source.decClockHOLFinite) childSize]
        | some result =>
          cases result with
          | error =>
            obtain ⟨after,targetBody,bodyBound⟩ := bodyError ctxt source.decClockHOLFinite sourcePost (decClockCrepSemHOL target)
              registered entryPresent bodyState codeRel excpRel localsRel bodyRun
            refine ⟨after,?_,?_⟩
            · rw [comp,evalCrepSemHOLProgExact_while_holShape,targetEval]
              simp [zeroBits,targetClock,targetBody,exitLoopCrepResult]
            · rw [comp,CrepSteps.steps_while,targetEval]
              simp only [if_pos (show word ≠ 0 ∧ target.clock ≠ 0 from ⟨zero,targetClock⟩),targetBody,sourceCount]
              nlinarith [Nat.mul_le_mul_right (controlSteps (progToHOL body) source.decClockHOLFinite) childSize]
          | «break» | «continue» => exact False.elim bodyScope
          | timeOut | returned _ | finalFfi _ | exception _ _ => simp at run

private theorem supportedErrorBridge {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ErrorBridge scope program := by
  induction supported with
  | skip => exact errorSkip
  | assign name member scalar => exact errorAssign name member scalar
  | decl name scalar body ih => exact errorDecl name scalar ih
  | seq a b iha ihb => exact errorSeq a iha ihb
  | ite scalar a b iha ihb => exact errorIte scalar iha ihb
  | «while» scalar body ih => exact errorWhile scalar body ih
  | ret scalar => exact errorReturn scalar

/-- Source errors in the supported fragment are preserved by the actual
compiled Crep program, with a bound determined by its size and the source
control visits. -/
theorem supported_compiler_error {σ : Type} {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (ctxt : PanToCrepContextExact 64)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (registered : ScopeRelation scope ctxt) (present : ScalarScopePresent scope source)
    (stateRel : panToCrepStateRelFiniteExact source target) (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (run : source.evaluateHOLFiniteState (progToHOL program) = (some .error,sourceFinal)) :
    ∃ targetFinal, evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (progToHOL program)) = (some .error,targetFinal) ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (progToHOL program)) target ≤
        3 * CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL program)) * controlSteps (progToHOL program) source :=
  supportedErrorBridge supported ctxt source sourceFinal target registered present stateRel codeRel excpRel localsRel run
end SteppedFlapjack.Concrete
