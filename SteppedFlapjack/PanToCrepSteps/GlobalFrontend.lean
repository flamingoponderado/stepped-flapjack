import SteppedFlapjack.PanToCrepSteps.GlobalInitializers
import SteppedFlapjack.PanToCrepSteps.WhileSteps
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-- Scalar expressions whose global references are resolved by the actual
    global layout. Flat fields are selected only at valid indices. -/
inductive GlobalScalar {width : Nat} [NeZero width]
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width) : ExpHOL width → Prop
  | local {e} : FrontendScalar ctxt e → GlobalScalar globals ctxt e
  | globalWord (name offset) : globals.globals.lookup name = some (.one,offset) →
      GlobalScalar globals ctxt (.var .global name)
  | globalField (name offset index count) : index < count →
      globals.globals.lookup name = some (.comb (List.replicate count .one),offset) →
      GlobalScalar globals ctxt (.rfield index (.var .global name))
  | load {address} : GlobalScalar globals ctxt address → GlobalScalar globals ctxt (.load .one address)
  | op (operator) {a b} : GlobalScalar globals ctxt a → GlobalScalar globals ctxt b →
      GlobalScalar globals ctxt (.op operator [a,b])
  | cmp (operator) {a b} : GlobalScalar globals ctxt a → GlobalScalar globals ctxt b →
      GlobalScalar globals ctxt (.cmp operator a b)
  | shift (operator) {a b} : GlobalScalar globals ctxt a → GlobalScalar globals ctxt b →
      GlobalScalar globals ctxt (.shift operator a b)

/-- Global lowering maps every supported scalar to the existing frontend. -/
theorem globalScalar_compiled {width : Nat} [NeZero width]
    {globals : PanGlobalsContextExact width} {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (h : GlobalScalar globals ctxt e) : FrontendScalar ctxt (compileExpExactHOL globals e) := by
  induction h with
  | «local» h => exact globalCompile_frontendScalar globals h
  | globalWord name offset found => exact globalCompile_globalWord globals ctxt name offset found
  | globalField name offset index count valid found => exact globalCompile_globalField globals ctxt name offset index count valid found
  | load h ih => simpa [compileExpExactHOL] using FrontendScalar.load ih
  | op operator a b iha ihb => simpa [compileExpExactHOL,compileExpExactHOLList] using FrontendScalar.op operator iha ihb
  | cmp operator a b iha ihb => simpa [compileExpExactHOL] using FrontendScalar.cmp operator iha ihb
  | shift operator a b iha ihb => simpa [compileExpExactHOL] using FrontendScalar.shift operator iha ihb

theorem globalScalar_list_compiled {width : Nat} [NeZero width]
    {globals : PanGlobalsContextExact width} {ctxt : PanToCrepContextExact width}
    (fields : List (ExpHOL width)) (h : ∀ e ∈ fields, GlobalScalar globals ctxt e) :
    ∀ e ∈ compileExpExactHOLList globals fields, FrontendScalar ctxt e := by
  induction fields with
  | nil => simp [compileExpExactHOLList]
  | cons e es ih =>
    intro x hx
    simp only [compileExpExactHOLList,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact globalScalar_compiled (h e (by simp))
    · exact ih (fun y hy => h y (by simp [hy])) x hx

/-- Programs with scalar globals and flat global structs lower to the proven
    frontend. Layout lookup is tracked directly in the fragment. -/
inductive GlobalFrontend {width : Nat} [NeZero width] (globals : PanGlobalsContextExact width) :
    PanToCrepContextExact width → ProgHOL width → Prop
  | skip {ctxt} : GlobalFrontend globals ctxt .skip
  | store {ctxt a v} : GlobalScalar globals ctxt a → GlobalScalar globals ctxt v → GlobalFrontend globals ctxt (.store a v)
  | assignLocal {ctxt name e} (reg : Nat) : ctxt.vars.lookup name = some (.one,[reg]) →
      GlobalScalar globals ctxt e → GlobalFrontend globals ctxt (.assign .local name e)
  | assignGlobal {ctxt name offset e} : globals.globals.lookup name = some (.one,offset) →
      GlobalScalar globals ctxt e → GlobalFrontend globals ctxt (.assign .global name e)
  | assignGlobalStruct {ctxt name offset fields} :
      globals.globals.lookup name = some (.comb (List.replicate fields.length .one),offset) →
      (∀ e ∈ fields, GlobalScalar globals ctxt e) → GlobalFrontend globals ctxt (.assign .global name (.rstruct fields))
  | decl {ctxt name e body} : GlobalScalar globals ctxt e →
      GlobalFrontend globals (scalarDeclContext ctxt name) body → GlobalFrontend globals ctxt (.dec name .one e body)
  | seq {ctxt a b} : GlobalFrontend globals ctxt a → GlobalFrontend globals ctxt b → GlobalFrontend globals ctxt (.seq a b)
  | ite {ctxt e a b} : GlobalScalar globals ctxt e → GlobalFrontend globals ctxt a → GlobalFrontend globals ctxt b →
      GlobalFrontend globals ctxt (.ite e a b)
  | while {ctxt e body} : GlobalScalar globals ctxt e → GlobalFrontend globals ctxt body → GlobalFrontend globals ctxt (.while e body)
  | ret {ctxt e} : GlobalScalar globals ctxt e → GlobalFrontend globals ctxt (.return e)

/-- Global reads and writes, including flat struct assignment, are accepted by
    the existing general Crep frontend after the actual globals pass. -/
theorem globalFrontend_compiled {width : Nat} [NeZero width]
    {globals : PanGlobalsContextExact width} {ctxt : PanToCrepContextExact width} {p : ProgHOL width}
    (h : GlobalFrontend globals ctxt p) : FrontendProgram ctxt (compileProgExactHOL globals p) := by
  induction h with
  | skip => simpa only [compileProgExactHOL] using (FrontendProgram.skip (ctxt := _))
  | store a v => simpa only [compileProgExactHOL] using FrontendProgram.store (globalScalar_compiled a) (globalScalar_compiled v)
  | assignLocal reg found e => simpa only [compileProgExactHOL] using FrontendProgram.assign reg found (globalScalar_compiled e)
  | assignGlobal found e =>
    simp only [compileProgExactHOL,found]
    exact .store (.op .sub .topAddr (.const _)) (globalScalar_compiled e)
  | assignGlobalStruct found fields =>
    simp only [compileProgExactHOL,found,compileExpExactHOL]
    exact .storeStruct (.op .sub .topAddr (.const _)) (globalScalar_list_compiled _ fields)
  | decl e body ih => simpa only [compileProgExactHOL] using FrontendProgram.decl (globalScalar_compiled e) ih
  | seq a b iha ihb => simpa only [compileProgExactHOL] using FrontendProgram.seq iha ihb
  | ite e a b iha ihb => simpa only [compileProgExactHOL] using FrontendProgram.ite (globalScalar_compiled e) iha ihb
  | «while» e body ih => simpa only [compileProgExactHOL] using FrontendProgram.while (globalScalar_compiled e) ih
  | ret e => simpa only [compileProgExactHOL] using FrontendProgram.ret (globalScalar_compiled e)
/-- Globals lowering preserves absence of loops for this fragment. -/
theorem globalFrontend_noWhile {width : Nat} [NeZero width]
    {globals : PanGlobalsContextExact width} {ctxt : PanToCrepContextExact width} {p : ProgHOL width}
    (h : GlobalFrontend globals ctxt p) (loopFree : noWhile p = true) :
    noWhile (compileProgExactHOL globals p) = true := by
  induction h <;> simp_all [noWhile,compileProgExactHOL]

/-- A loop-free global program has a static compiled-Crep visit bound. -/
theorem globalFrontend_staticSteps {width : Nat} [NeZero width] {σ : Type}
    {globals : PanGlobalsContextExact width} {ctxt : PanToCrepContextExact width} {p : ProgHOL width}
    (h : GlobalFrontend globals ctxt p) (loopFree : noWhile p = true)
    (target : CrepSemHOLState width σ) :
    SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) target ≤
      sizeOf (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) := by
  exact SteppedFlapjack.CrepSteps.staticProgram_steps
    (frontendLoopFree_static (globalFrontend_compiled h) (globalFrontend_noWhile h loopFree)) target
/-- A non-error loop-free global run lowers through both global and Crep
    compilation with a visit bound computed from the generated Crep code. -/
theorem globalFrontend_correct_static {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width) (p : ProgHOL width)
    (shape : GlobalFrontend globals ctxt p) (loopFree : noWhile p = true)
    (source sourceFinal target : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (crep : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (globalRel : panGlobalsStateRelHOLExact true globals source target)
    (stateRel : panToCrepStateRelFiniteExact target crep)
    (codeRel : codeRelExactHOLW ctxt target.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids target.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt target.locals crep.locals) :
    ∃ targetFinal crepResult crepFinal,
      target.evaluateHOLFiniteState (compileProgExactHOL globals p) = (result,targetFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL result) globals sourceFinal targetFinal ∧
      evalCrepSemHOLProgExact crep (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) = (crepResult,crepFinal) ∧
      panToCrepStateRelFiniteExact targetFinal crepFinal ∧
      pcCompileCorrectResultRel ctxt targetFinal crepFinal result crepResult ∧
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) crep ≤
        sizeOf (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) := by
  obtain ⟨targetFinal,targetRun,globalFinal⟩ :=
    PanGlobalsCompileCorrectAssembly.compileCorrectHOL
      p source result globals target sourceFinal ⟨globalRel,run,nonerror⟩
  obtain ⟨crepResult,crepFinal,crepRun,finalRel,_,_,resultRel,_⟩ := frontend_correct_with_steps
    ctxt (compileProgExactHOL globals p) (globalFrontend_compiled shape) target targetFinal result crep
    (controlSteps (compileProgExactHOL globals p) target) targetRun nonerror (Nat.le_refl _)
    stateRel codeRel excpRel localsRel
  exact ⟨targetFinal,crepResult,crepFinal,targetRun,globalFinal,crepRun,finalRel,resultRel,
    globalFrontend_staticSteps shape loopFree crep⟩

/-- Call-aware global programs use the same scalar-global layout checks and
    allow ordinary or tail calls in arbitrary control-flow positions. -/
inductive GlobalCallFrontend {width : Nat} [NeZero width] (globals : PanGlobalsContextExact width) :
    PanToCrepContextExact width → ProgHOL width → Prop
  | base {ctxt p} : GlobalFrontend globals ctxt p → GlobalCallFrontend globals ctxt p
  | tail {ctxt name args} : (∀ e ∈ args, GlobalScalar globals ctxt e) →
      GlobalCallFrontend globals ctxt (.call none name args)
  | decCall {ctxt name shape fname args body} : (∀ e ∈ args, GlobalScalar globals ctxt e) →
      GlobalCallFrontend globals (decCallCtxt ctxt name shape) body →
      GlobalCallFrontend globals ctxt (.decCall name shape fname args body)
  | decl {ctxt name e body} : GlobalScalar globals ctxt e →
      GlobalCallFrontend globals (scalarDeclContext ctxt name) body →
      GlobalCallFrontend globals ctxt (.dec name .one e body)
  | seq {ctxt a b} : GlobalCallFrontend globals ctxt a → GlobalCallFrontend globals ctxt b →
      GlobalCallFrontend globals ctxt (.seq a b)
  | ite {ctxt e a b} : GlobalScalar globals ctxt e → GlobalCallFrontend globals ctxt a →
      GlobalCallFrontend globals ctxt b → GlobalCallFrontend globals ctxt (.ite e a b)
  | while {ctxt e body} : GlobalScalar globals ctxt e → GlobalCallFrontend globals ctxt body →
      GlobalCallFrontend globals ctxt (.while e body)

/-- Global lowering produces the existing call-aware frontend shape. -/
theorem globalCallFrontend_compiled {width : Nat} [NeZero width]
    {globals : PanGlobalsContextExact width} {ctxt : PanToCrepContextExact width} {p : ProgHOL width}
    (h : GlobalCallFrontend globals ctxt p) : CallFrontend ctxt (compileProgExactHOL globals p) := by
  induction h with
  | base h => exact .base (globalFrontend_compiled h)
  | tail args => simpa only [compileProgExactHOL] using CallFrontend.tail (globalScalar_list_compiled _ args)
  | decCall args body ih => simpa only [compileProgExactHOL] using CallFrontend.decCall (globalScalar_list_compiled _ args) ih
  | decl e body ih => simpa only [compileProgExactHOL] using CallFrontend.decl (globalScalar_compiled e) ih
  | seq a b iha ihb => simpa only [compileProgExactHOL] using CallFrontend.seq iha ihb
  | ite e a b iha ihb => simpa only [compileProgExactHOL] using CallFrontend.ite (globalScalar_compiled e) iha ihb
  | «while» e body ih => simpa only [compileProgExactHOL] using CallFrontend.while (globalScalar_compiled e) ih

end SteppedFlapjack.PanToCrepSteps
