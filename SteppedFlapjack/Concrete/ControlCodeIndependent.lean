import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals
import SteppedFlapjack.Concrete.CodeIndependent
import SteppedFlapjack.Concrete.GlobalControl
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Prime
import Flapjack.Pancake.Proofs.PanSimp.CompileCorrect
import SteppedFlapjack.PanToCrepSteps.ControlSteps
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps
private def ControlCode (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (source : PanSemStateFiniteExact 64 σ)
      (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)),
    controlSteps (progToHOL program) {source with code := code} = controlSteps (progToHOL program) source

private theorem controlSkip : ControlCode .skip := by
  intro σ source code
  simp [progToHOL,controlSteps.eq_def]

private theorem controlReturn {expression : Exp (RiscV.Word 64)} : ControlCode (.return expression) := by
  intro σ source code
  simp [progToHOL,controlSteps.eq_def]

private theorem controlAssign (name : VarName) {expression : Exp (RiscV.Word 64)} : ControlCode (.assign .local name expression) := by
  intro σ source code
  simp [progToHOL,controlSteps.eq_def]

private theorem controlSeq {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (aSupported : SupportedIn scope a) (aCode : ControlCode a) (bCode : ControlCode b) : ControlCode (.seq a b) := by
  intro σ source code
  simp only [progToHOL,controlSteps_seq]
  have runEq := supportedIn_code_irrel aSupported source code
  rcases run : source.evaluateHOLFiniteState (progToHOL a) with ⟨result,post⟩
  rw [run] at runEq
  simp only at runEq
  rw [runEq,aCode]
  cases result with
  | none => simpa using bCode post code
  | some _ => rfl

private theorem controlIte {scope : List VarName} {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (aCode : ControlCode a) (bCode : ControlCode b) : ControlCode (.ite condition a b) := by
  intro σ source code
  simp only [progToHOL,controlSteps_ite]
  rw [scalar_eval_code_irrel scalar source code]
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
  | none => rfl
  | some value =>
    cases value with
    | rStruct _ | nStruct _ _ => rfl
    | val word =>
      cases word with
      | word n =>
        by_cases zero : n = 0
        · simpa [zero] using bCode source code
        · have zeroBits : n ≠ (0#64) := by simpa using zero
          simpa [zeroBits] using aCode source code

private theorem controlDecl {scope : List VarName} (name : VarName) {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope initializer) (bodyCode : ControlCode body) : ControlCode (.dec name .one initializer body) := by
  intro σ source code
  simp only [progToHOL,shapeToHOL]
  have evalEq := scalar_eval_code_irrel scalar source code
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) with
  | none =>
    rw [controlSteps.eq_def,controlSteps.eq_def]
    simp only
    rw [evalEq,h]
  | some value =>
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · rw [controlSteps_dec _ _ _ _ _ value (evalEq.trans h) valid,controlSteps_dec _ _ _ _ _ value h valid]
      simpa [setVarHOLFinite] using bodyCode (setVarHOLFinite (ofString name) value source) code
    · rw [controlSteps.eq_def,controlSteps.eq_def]
      simp only
      rw [evalEq,h]
      simp [valid]

private theorem controlWhile {scope : List VarName} {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (bodySupported : SupportedIn scope body) (bodyCode : ControlCode body) : ControlCode (.while condition body) := by
  intro σ source code
  induction hc : source.clock using Nat.strongRecOn generalizing source with
  | _ clock ih =>
    rw [← hc]
    simp only [progToHOL]
    rw [controlSteps_while,controlSteps_while]
    have evalEq := scalar_eval_code_irrel scalar source code
    rw [evalEq]
    cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
    | none => rfl
    | some value =>
      cases value with
      | rStruct _ | nStruct _ _ => rfl
      | val word =>
        cases word with
        | word n =>
          by_cases active : n ≠ 0 ∧ source.clock ≠ 0
          · simp only [if_pos active]
            rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨result,post⟩
            have bodyRunCode := supportedIn_code_irrel bodySupported source.decClockHOLFinite code
            rw [bodyRun] at bodyRunCode
            simp only at bodyRunCode
            have bodyRunCode' : ({source with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) =
                (result,{post with code := code}) := by simpa [decClockHOLFinite] using bodyRunCode
            rw [bodyRunCode']
            have child : controlSteps (progToHOL body) ({source with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite =
                controlSteps (progToHOL body) source.decClockHOLFinite := by simpa [decClockHOLFinite] using bodyCode source.decClockHOLFinite code
            rw [child]
            have mono := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
            rw [bodyRun] at mono
            have smaller : post.clock < clock := by simp [decClockHOLFinite] at mono; omega
            have recursive := ih post.clock smaller post rfl
            simp only [progToHOL] at recursive
            cases result with
            | none => simp [recursive]
            | some r => cases r <;> simp [recursive]
          · simp only [if_neg active]

private theorem supportedControlCode {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ControlCode program := by
  induction supported with
  | skip => exact controlSkip
  | assign name member scalar => exact controlAssign name
  | decl name scalar body ih => exact controlDecl name scalar ih
  | seq a b iha ihb => exact controlSeq a iha ihb
  | ite scalar a b iha ihb => exact controlIte scalar iha ihb
  | «while» scalar body ih => exact controlWhile scalar body ih
  | ret scalar => exact controlReturn

theorem supported_control_code_irrel {σ : Type} {program : Prog (RiscV.Word 64)} (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    controlSteps (progToHOL program) {source with code := code} = controlSteps (progToHOL program) source :=
  supportedControlCode supported.1 source code

private def FpermControl (limit : Nat) (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (f g : MlString) (source : PanSemStateFiniteExact 64 σ),
    source.clock ≤ limit → GlobalTableSupported source.code →
    controlSteps (fpermHOL f g (progToHOL program)) {source with code := fpermCodeHOL f g source.code} =
      controlSteps (progToHOL program) source

private theorem callSupported_fpermControl (limit : Nat) :
    ∀ scope program, CallSupportedIn scope program → FpermControl limit program := by
  induction limit using Nat.strongRecOn with
  | _ limit clockIH =>
    intro scope program supported
    induction supported with
    | base h =>
      intro σ f g source budget table
      rw [supportedIn_fperm h f g]
      exact supportedControlCode h source (fpermCodeHOL f g source.code)
    | tail name args scalar =>
      intro σ f g source budget table
      simp only [progToHOL,fpermHOL]
      have targetArgs := PanSimp.evalListCodeUpd (fpermCodeHOL f g source.code) source (args.map expToHOL)
      cases argsEval : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a))
          (args.map expToHOL) with
      | none =>
        rw [controlSteps.eq_def,controlSteps.eq_def]
        simp only [targetArgs,argsEval]
      | some values =>
        have targetLookup := lookupCodeFpermCodeHOL f g source.code (ofString name) values
        change lookupCodeHOLFinite (fpermCodeHOL f g source.code).lookup (fpermName f g (ofString name)) values =
          (lookupCodeHOLFinite source.code.lookup (ofString name) values).map (fun entry =>
            (fpermHOL f g entry.1,entry.2.1,entry.2.2)) at targetLookup
        cases found : lookupCodeHOLFinite source.code.lookup (ofString name) values with
        | none =>
          rw [found] at targetLookup
          simp only [Option.map_none] at targetLookup
          rw [controlSteps.eq_def,controlSteps.eq_def]
          simp only [targetArgs,argsEval,targetLookup,found]
        | some entry =>
          obtain ⟨body,locals,rsh⟩ := entry
          rw [found] at targetLookup
          simp only [Option.map_some] at targetLookup
          by_cases noClock : source.clock = 0
          · rw [controlSteps.eq_def,controlSteps.eq_def]
            simp only [targetArgs,argsEval,targetLookup,found,if_pos noClock]
          · obtain ⟨bodyScope,callee,bodyEq,calleeShape⟩ := table _ _ _ _ _ found
            subst body
            have smaller : (callEntryStateHOLFinite source locals).clock < limit := by
              simp only [callEntryStateHOLFinite]
              omega
            have bodyControl : FpermControl (callEntryStateHOLFinite source locals).clock callee :=
              clockIH _ smaller bodyScope callee calleeShape
            have bodyTable : GlobalTableSupported (callEntryStateHOLFinite source locals).code := table
            have bodyBound := bodyControl f g (callEntryStateHOLFinite source locals) (Nat.le_refl _) bodyTable
            have targetArgs' : @evalListHOLFinite 64 σ _ {source with code := fpermCodeHOL f g source.code}
                (fun a => Classical.propDecidable (source.memaddrs a)) (args.map expToHOL) = some values := by
              rw [targetArgs,argsEval]
            rw [controlSteps_tailCall (fpermName f g (ofString name)) _ _ values (fpermHOL f g (progToHOL callee)) locals rsh
                targetArgs' targetLookup noClock,
              controlSteps_tailCall (ofString name) _ source values (progToHOL callee) locals rsh argsEval found noClock]
            simpa [callEntryStateHOLFinite] using bodyBound
    | @call scope dest name args cont scalar contShape contIH =>
      intro σ f g source budget table
      simp only [progToHOL,shapeToHOL,fpermHOL]
      have targetArgs := PanSimp.evalListCodeUpd (fpermCodeHOL f g source.code) source (args.map expToHOL)
      cases argsEval : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a))
          (args.map expToHOL) with
      | none =>
        rw [controlSteps.eq_def,controlSteps.eq_def]
        simp only [targetArgs,argsEval]
      | some values =>
        have targetLookup := lookupCodeFpermCodeHOL f g source.code (ofString name) values
        change lookupCodeHOLFinite (fpermCodeHOL f g source.code).lookup (fpermName f g (ofString name)) values =
          (lookupCodeHOLFinite source.code.lookup (ofString name) values).map (fun entry =>
            (fpermHOL f g entry.1,entry.2.1,entry.2.2)) at targetLookup
        cases found : lookupCodeHOLFinite source.code.lookup (ofString name) values with
        | none =>
          rw [found] at targetLookup
          simp only [Option.map_none] at targetLookup
          rw [controlSteps.eq_def,controlSteps.eq_def]
          simp only [targetArgs,argsEval,targetLookup,found]
        | some entry =>
          obtain ⟨body,locals,rsh⟩ := entry
          rw [found] at targetLookup
          simp only [Option.map_some] at targetLookup
          by_cases noClock : source.clock = 0
          · rw [controlSteps.eq_def,controlSteps.eq_def]
            simp only [targetArgs,argsEval,targetLookup,found,if_pos noClock]
          · obtain ⟨bodyScope,callee,bodyEq,calleeShape⟩ := table _ _ _ _ _ found
            subst body
            have smaller : (callEntryStateHOLFinite source locals).clock < limit := by
              simp only [callEntryStateHOLFinite]
              omega
            have bodyControl : FpermControl (callEntryStateHOLFinite source locals).clock callee :=
              clockIH _ smaller bodyScope callee calleeShape
            have bodyTable : GlobalTableSupported (callEntryStateHOLFinite source locals).code := table
            have bodyBound := bodyControl f g (callEntryStateHOLFinite source locals) (Nat.le_refl _) bodyTable
            have bodyBound' : controlSteps (fpermHOL f g (progToHOL callee))
                (callEntryStateHOLFinite {source with code := fpermCodeHOL f g source.code} locals) =
                controlSteps (progToHOL callee) (callEntryStateHOLFinite source locals) := by
              simpa [callEntryStateHOLFinite] using bodyBound
            have targetArgs' : @evalListHOLFinite 64 σ _ {source with code := fpermCodeHOL f g source.code}
                (fun a => Classical.propDecidable (source.memaddrs a)) (args.map expToHOL) = some values := by
              rw [targetArgs,argsEval]
            rcases bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState (progToHOL callee) with ⟨result,post⟩
            have targetRun := evaluateFpermHOL f g (progToHOL callee) (callEntryStateHOLFinite source locals) result post bodyRun
            have targetRun' : (callEntryStateHOLFinite {source with code := fpermCodeHOL f g source.code} locals).evaluateHOLFiniteState
                (fpermHOL f g (progToHOL callee)) = (result,{post with code := fpermCodeHOL f g post.code}) := by
              simpa [callEntryStateHOLFinite] using targetRun
            by_cases returned : ∃ value, result = some (.returned value)
            · obtain ⟨value,rfl⟩ := returned
              by_cases valid : shapeEqHOL (shapeOfHOLExact value) .one = true ∧ shapeEqHOL (shapeOfHOLExact value) rsh = true
              · rw [controlSteps_decCall_return (ofString dest) (fpermName f g (ofString name)) .one _ _ _ values
                  (fpermHOL f g (progToHOL callee)) locals rsh value {post with code := fpermCodeHOL f g post.code}
                  targetArgs' targetLookup noClock targetRun' valid.1 valid.2,
                controlSteps_decCall_return (ofString dest) (ofString name) .one _ _ source values (progToHOL callee) locals rsh value post
                  argsEval found noClock bodyRun valid.1 valid.2]
                have fixed : fixClockHOLFinite (callEntryStateHOLFinite source locals) (some (PanSemResultExact.returned value),post) =
                    (some (PanSemResultExact.returned value),post) := by rw [← bodyRun,fixClockHOLFinite_evaluateState]
                have targetFixed : fixClockHOLFinite (callEntryStateHOLFinite {source with code := fpermCodeHOL f g source.code} locals)
                    (some (PanSemResultExact.returned value),{post with code := fpermCodeHOL f g post.code}) =
                    (some (PanSemResultExact.returned value),{post with code := fpermCodeHOL f g post.code}) := by
                  rw [← targetRun',fixClockHOLFinite_evaluateState]
                simp only [fixed,targetFixed,bodyBound']
                let next := setVarHOLFinite (ofString dest) value {post with locals := source.locals}
                have postCode : post.code = source.code := by
                  have h := SemInitSupport.eval_code (callEntryStateHOLFinite source locals) (progToHOL callee)
                  rw [bodyRun] at h
                  simpa [callEntryStateHOLFinite] using h
                have nextTable : GlobalTableSupported next.code := by simpa [next,setVarHOLFinite,postCode] using table
                have nextSmall : next.clock < limit := by
                  have h := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source locals) (progToHOL callee)
                  rw [bodyRun] at h
                  simp only [next,setVarHOLFinite,callEntryStateHOLFinite] at h ⊢
                  omega
                have nextControl : FpermControl next.clock cont := clockIH _ nextSmall (dest :: scope) cont contShape
                have nextBound := nextControl f g next (Nat.le_refl _) nextTable
                simpa [next,setVarHOLFinite] using nextBound
              · have bad : (shapeEqHOL (shapeOfHOLExact value) .one && shapeEqHOL (shapeOfHOLExact value) rsh) = false := by
                  cases h₁ : shapeEqHOL (shapeOfHOLExact value) .one <;>
                    cases h₂ : shapeEqHOL (shapeOfHOLExact value) rsh <;> simp_all
                have sourceSmall : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
                    ((callEntryStateHOLFinite source locals).clock,sizeOf (progToHOL callee))
                    (source.clock,sizeOf (.decCall (ofString dest) .one (ofString name) (args.map expToHOL) (progToHOL cont) : ProgHOL 64)) := by
                  apply Prod.Lex.left
                  simp only [callEntryStateHOLFinite]
                  omega
                have targetSmall : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
                    ((callEntryStateHOLFinite {source with code := fpermCodeHOL f g source.code} locals).clock,sizeOf (fpermHOL f g (progToHOL callee)))
                    (source.clock,sizeOf (.decCall (ofString dest) .one (fpermName f g (ofString name)) (args.map expToHOL) (fpermHOL f g (progToHOL cont)) : ProgHOL 64)) := by
                  apply Prod.Lex.left
                  simp only [callEntryStateHOLFinite]
                  omega
                rw [controlSteps.eq_def,controlSteps.eq_def (.decCall (ofString dest) .one (ofString name) (args.map expToHOL) (progToHOL cont))]
                simp only [targetArgs,argsEval,targetLookup,found,if_neg noClock,bodyRun,targetRun',bad,Bool.false_eq_true,if_false,
                  dif_pos sourceSmall,dif_pos targetSmall]
                rw [bodyBound']
            · have terminal : ∀ value, result ≠ some (.returned value) := by
                intro value h; exact returned ⟨value,h⟩
              rw [controlSteps_decCall_terminal (ofString dest) (fpermName f g (ofString name)) .one _ _ _ values
                  (fpermHOL f g (progToHOL callee)) locals rsh result {post with code := fpermCodeHOL f g post.code}
                  targetArgs' targetLookup noClock targetRun' terminal,
                controlSteps_decCall_terminal (ofString dest) (ofString name) .one _ _ source values (progToHOL callee) locals rsh result post
                  argsEval found noClock bodyRun terminal,bodyBound']
    | @decl scope name initializer body scalar bodyShape ih =>
      intro σ f g source budget table
      simp only [progToHOL,shapeToHOL,fpermHOL]
      have evalEq := scalar_eval_code_irrel scalar source (fpermCodeHOL f g source.code)
      cases evaluated : @evalHOLExact 64 σ _ source.toExact
          (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) with
      | none =>
        rw [controlSteps.eq_def,controlSteps.eq_def]
        simp only
        rw [evalEq,evaluated]
      | some value =>
        by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
        · rw [controlSteps_dec _ _ _ _ _ value (evalEq.trans evaluated) valid,
            controlSteps_dec _ _ _ _ _ value evaluated valid]
          have childBudget : (setVarHOLFinite (ofString name) value source).clock ≤ limit := by
            simpa [setVarHOLFinite] using budget
          have childTable : GlobalTableSupported (setVarHOLFinite (ofString name) value source).code := by
            simpa [setVarHOLFinite] using table
          simpa [setVarHOLFinite] using ih f g (setVarHOLFinite (ofString name) value source) childBudget childTable
        · rw [controlSteps.eq_def,controlSteps.eq_def]
          simp only
          rw [evalEq,evaluated]
          simp [valid]
    | @seq scope a b ashape bshape iha ihb =>
      intro σ f g source budget table
      simp only [progToHOL,fpermHOL,controlSteps_seq]
      rcases run : source.evaluateHOLFiniteState (progToHOL a) with ⟨result,post⟩
      have targetRun := evaluateFpermHOL f g (progToHOL a) source result post run
      rw [targetRun,iha f g source budget table]
      cases result with
      | none =>
        have postClock : post.clock ≤ limit := by
          have h := evaluateHOLFiniteState_clock_le source (progToHOL a)
          rw [run] at h
          simp only at h
          omega
        have postCode : post.code = source.code := by
          have h := SemInitSupport.eval_code source (progToHOL a)
          rw [run] at h
          exact h
        have postTable : GlobalTableSupported post.code := by rw [postCode]; exact table
        simpa using ihb f g post postClock postTable
      | some r => rfl
    | @ite scope condition a b scalar ashape bshape iha ihb =>
      intro σ f g source budget table
      simp only [progToHOL,fpermHOL,controlSteps_ite]
      rw [scalar_eval_code_irrel scalar source (fpermCodeHOL f g source.code)]
      cases evaluated : @evalHOLExact 64 σ _ source.toExact
          (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
      | none => rfl
      | some value =>
        cases value with
        | rStruct _ | nStruct _ _ => rfl
        | val word =>
          cases word with
          | word n =>
            by_cases zero : n = 0
            · simpa [zero] using ihb f g source budget table
            · have zeroBits : n ≠ (0#64) := by simpa using zero
              simpa [zeroBits] using iha f g source budget table
    | @«while» scope condition body scalar bodyShape ih =>
      intro σ f g source budget table
      simp only [progToHOL,fpermHOL]
      rw [controlSteps_while,controlSteps_while]
      rw [scalar_eval_code_irrel scalar source (fpermCodeHOL f g source.code)]
      cases evaluated : @evalHOLExact 64 σ _ source.toExact
          (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
      | none => rfl
      | some value =>
        cases value with
        | rStruct _ | nStruct _ _ => rfl
        | val word =>
          cases word with
          | word n =>
            by_cases active : n ≠ 0 ∧ source.clock ≠ 0
            · simp only [if_pos active]
              rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨result,post⟩
              have targetRun := evaluateFpermHOL f g (progToHOL body) source.decClockHOLFinite result post bodyRun
              have targetRun' : ({source with code := fpermCodeHOL f g source.code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite.evaluateHOLFiniteState
                  (fpermHOL f g (progToHOL body)) = (result,{post with code := fpermCodeHOL f g post.code}) := by
                simpa [decClockHOLFinite] using targetRun
              rw [targetRun']
              have childBudget : source.decClockHOLFinite.clock ≤ limit := by simp only [decClockHOLFinite]; omega
              have childTable : GlobalTableSupported source.decClockHOLFinite.code := table
              have child := ih f g source.decClockHOLFinite childBudget childTable
              have child' : controlSteps (fpermHOL f g (progToHOL body))
                  ({source with code := fpermCodeHOL f g source.code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite =
                  controlSteps (progToHOL body) source.decClockHOLFinite := by simpa [decClockHOLFinite] using child
              rw [child']
              have postCode : post.code = source.code := by
                have h := SemInitSupport.eval_code source.decClockHOLFinite (progToHOL body)
                rw [bodyRun] at h
                simpa [decClockHOLFinite] using h
              have postTable : GlobalTableSupported post.code := by rw [postCode]; exact table
              have smaller : post.clock < limit := by
                have h := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
                rw [bodyRun] at h
                simp only [decClockHOLFinite] at h
                omega
              have loopControl : FpermControl post.clock (.while condition body) :=
                clockIH post.clock smaller scope (.while condition body) (.while scalar bodyShape)
              cases result with
              | none =>
                simpa [progToHOL,fpermHOL] using loopControl f g post (Nat.le_refl _) postTable
              | some r =>
                cases r with
                | «continue» =>
                  simpa [progToHOL,fpermHOL] using loopControl f g post (Nat.le_refl _) postTable
                | «break» | error | timeOut | returned _ | finalFfi _ | exception _ _ => rfl
            · simp only [if_neg active]

/-- Function renaming preserves the exact control-visit count for the supported call table. -/
theorem callSupported_fperm_control {scope : List VarName} {σ : Type}
    {program : Prog (RiscV.Word 64)} (supported : CallSupportedIn scope program)
    (f g : MlString) (source : PanSemStateFiniteExact 64 σ) (table : GlobalTableSupported source.code) :
    controlSteps (fpermHOL f g (progToHOL program)) {source with code := fpermCodeHOL f g source.code} =
      controlSteps (progToHOL program) source :=
  callSupported_fpermControl source.clock scope program supported f g source (Nat.le_refl _) table

private theorem supportedIn_rename_identity {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (f g : FunName) : globalRenameProg f g program = program := by
  induction supported <;> simp_all [globalRenameProg]

/-- Function renaming retains the supported call-aware fragment. -/
theorem callSupported_globalRename {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) (f g : FunName) :
    CallSupportedIn scope (globalRenameProg f g program) := by
  induction supported with
  | base h => simpa [supportedIn_rename_identity h f g] using (CallSupportedIn.base h)
  | tail name args scalar => simpa only [globalRenameProg] using (CallSupportedIn.tail (globalRenameFunctionName f g name) args scalar)
  | call dest name args scalar cont ih =>
    simpa only [globalRenameProg] using (CallSupportedIn.call dest (globalRenameFunctionName f g name) args scalar ih)
  | decl name scalar body ih => simpa only [globalRenameProg] using (CallSupportedIn.decl name scalar ih)
  | seq a b iha ihb => simpa only [globalRenameProg] using (CallSupportedIn.seq iha ihb)
  | ite scalar a b iha ihb => simpa only [globalRenameProg] using (CallSupportedIn.ite scalar iha ihb)
  | «while» scalar body ih => simpa only [globalRenameProg] using (CallSupportedIn.while scalar ih)

/-- Renaming a representable call-aware body yields another such body. -/
theorem callSupported_fperm_shape {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) (ranged : ProgByteRanged program) (f g : MlString) :
    ∃ renamed : Prog (RiscV.Word 64), fpermHOL f g (progToHOL program) = progToHOL renamed ∧
      CallSupportedIn scope renamed := by
  let renamed := globalRenameProg (toStringOfBytes f) (toStringOfBytes g) program
  have bridge := progOfHOL_fpermHOL f g (progToHOL program)
  rw [progOfHOL_progToHOL program ranged] at bridge
  have encoded := congrArg progToHOL bridge
  rw [progToHOL_progOfHOL] at encoded
  exact ⟨renamed,encoded,callSupported_globalRename supported _ _⟩

/-- Renaming a representable supported function table preserves its support. -/
theorem fperm_globalTableSupported (source : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (f g : MlString)
    (table : ∀ name values body locals rsh, lookupCodeHOLFinite source.lookup name values = some (body,locals,rsh) →
      ∃ scope, ∃ program : Prog (RiscV.Word 64), body = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program) :
    GlobalTableSupported (fpermCodeHOL f g source) := by
  intro name values body locals rsh targetFound
  have lookup := lookupCodeFpermCodeHOL f g source (fpermName f g name) values
  simp only [fpermName_cancel] at lookup
  change lookupCodeHOLFinite (fpermCodeHOL f g source).lookup name values =
    (lookupCodeHOLFinite source.lookup (fpermName f g name) values).map
      (fun entry => (fpermHOL f g entry.1,entry.2.1,entry.2.2)) at lookup
  rw [targetFound] at lookup
  cases found : lookupCodeHOLFinite source.lookup (fpermName f g name) values with
  | none => simp [found] at lookup
  | some entry =>
    obtain ⟨original,originalLocals,originalShape⟩ := entry
    simp only [found,Option.map_some,Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨bodyEq,localsEq,shapeEq⟩ := lookup
    subst locals
    subst rsh
    obtain ⟨scope,program,originalEq,supported,ranged⟩ := table _ _ _ _ _ found
    obtain ⟨renamed,renameEq,renameSupported⟩ := callSupported_fperm_shape supported ranged f g
    refine ⟨scope,renamed,?_,renameSupported⟩
    rw [originalEq,renameEq] at bodyEq
    exact bodyEq


/-- Scalar call-supported functions produce a call-aware lowered declaration table. -/
theorem functionOnly_callFrontend_shapes (fs : List (FunDeclHOL 64)) (start : MlS)
    (body : ProgHOL 64) (rshape : ShapeHOL)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,rshape))
    (shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ program : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (ofString n,ShapeHOL.one)) ∧ entry.2.2.1 = progToHOL program ∧
        CallSupportedIn names program ∧ ProgByteRanged program) :
    ∀ entry ∈ functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start),
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL (compileTopExactHOL (fs.map DeclHOL.function) start))) entry.2.2.1 := by
  intro entry member
  rw [functionOnly_compileTop_functions fs start body rshape found] at member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact .seq (.base .skip) (.tail (by simp))
  · obtain ⟨renamed,renamedMember,rfl⟩ := List.mem_map.mp member
    rw [functionsFpermDecsHOL] at renamedMember
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp renamedMember
    obtain ⟨names,program,paramEq,bodyEq,supported,ranged⟩ := shapes original originalMember
    obtain ⟨renamedProgram,renamedEq,renamedSupported⟩ :=
      callSupported_fperm_shape supported ranged start (newMainNameHOL (fs.map DeclHOL.function))
    have fixed := callSupportedIn_globals_fixed renamedSupported (emptyGlobalsContext : PanGlobalsContextExact 64)
    rw [paramEq,bodyEq,renamedEq,fixed]
    simpa only [List.map_map,Function.comp_def] using
      callSupported_scalarFunction_frontend names renamedSupported
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)))
        (getEidsFromDeclsHOL (compileTopExactHOL (fs.map DeclHOL.function) start))

end SteppedFlapjack.Concrete
