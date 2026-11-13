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
  | store address value => intro σ source code; simp [progToHOL,controlSteps.eq_def]
  | assign name member scalar => exact controlAssign name
  | decl name scalar body ih => exact controlDecl name scalar ih
  | seq a b iha ihb => exact controlSeq a iha ihb
  | ite scalar a b iha ihb => exact controlIte scalar iha ihb
  | «while» scalar body ih => exact controlWhile scalar body ih
  | ret scalar => exact controlReturn

theorem supported_control_code_irrel {σ : Type} {program : Prog (RiscV.Word 64)} (supported : CallFreeSupported program)
    (source : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    controlSteps (progToHOL program) {source with code := code} = controlSteps (progToHOL program) source :=
  supportedControlCode supported.1 source code

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
