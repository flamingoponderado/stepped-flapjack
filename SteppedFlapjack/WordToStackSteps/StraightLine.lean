import SteppedFlapjack.WordToStackSteps.Instructions

/-! Quantitative compilation for loop-free, call-free WordSem programs. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackRemoveSteps
variable {width : Nat} [NeZero width]

/-- A recursively closed fragment with statically bounded compiled executions. -/
def straightWord : WordLangProgHOL (BitVec width) → Bool
  | .skip | .tick | .break _ | .continue _ | .ffi _ _ _ _ _ _ | .inst _ | .move _ _
  | .get _ _ | .set _ _ | .storeConsts _ _ _ _ _ | .locValue _ _ | .opCurrHeap _ _ _
  | .install _ _ _ _ _ | .codeBufferWrite _ _ | .dataBufferWrite _ _ => true
  | .seq a b | .ite _ _ _ a b => straightWord a && straightWord b
  | .mustTerminate p => straightWord p
  | _ => false

/-- Compilation preserves straight-line control flow for the fragment. -/
theorem straightWord_compiled (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (hp : straightWord p = true) (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    straightLine (compNative ac false p bs kf).1 = true := by
  cases h : p <;> simp_all only [straightWord, Bool.and_eq_true, Bool.false_eq_true]
  case skip => simp [compNative, straightLine]
  case tick => simp [compNative, straightLine]
  case «break» => simp [compNative, straightLine]
  case «continue» => simp [compNative, straightLine]
  case ffi => simp [compNative, straightLine]
  case inst i => exact straightLine_compileInst ac i bs kf
  case move priority moves => simp only [compNative]; exact straightLine_move moves kf
  case get => simp only [compNative]; apply straightLine_regWrite1; intro; rfl
  case set name exp =>
    cases name <;> cases exp <;> simp only [compNative]
    all_goals first | rfl | apply straightLine_stackLoad; rfl
  case storeConsts =>
    simp [compNative, straightLine]
  case locValue => simp only [compNative]; apply straightLine_regWrite1; intro; rfl
  case opCurrHeap =>
    simp only [compNative]
    apply straightLine_stackLoad
    apply straightLine_regWrite1
    intro; rfl
  case install => simp only [compNative]; apply straightLine_stackLoad; rfl
  case codeBufferWrite => simp only [compNative]; apply straightLine_stackLoad; rfl
  case dataBufferWrite => simp only [compNative]; apply straightLine_stackLoad; rfl
  case mustTerminate q =>
    simp only [compNative]
    exact straightWord_compiled ac q hp bs kf
  case seq a b =>
    simp only [compNative]
    rcases hc : compNative ac false a bs kf with ⟨ca, bs1⟩
    rcases hd : compNative ac false b bs1 kf with ⟨cb, bs2⟩
    simp only [straightLine, Bool.and_eq_true]
    constructor
    · simpa only [hc] using straightWord_compiled ac a hp.1 bs kf
    · simpa only [hd] using straightWord_compiled ac b hp.2 bs1 kf
  case ite cmp r ri a b =>
    simp only [compNative]
    rcases hc : compNative ac false a bs kf with ⟨ca, bs1⟩
    rcases hd : compNative ac false b bs1 kf with ⟨cb, bs2⟩
    have ha : straightLine ca = true := by simpa only [hc] using straightWord_compiled ac a hp.1 bs kf
    have hb : straightLine cb = true := by simpa only [hd] using straightWord_compiled ac b hp.2 bs1 kf
    cases ri with
    | reg n => simp only; apply straightLine_stackLoad; simp [straightLine, ha, hb]
    | imm i =>
      simp only
      split <;> simp [straightLine, straightLine_stackLoad, ha, hb]
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf <;> omega


/-- Loop-free and call-free WordSem programs in the fragment have a target
runtime bound computable from compilation, with the original semantic result. -/
theorem straightWord_simulation {C F : Type} (ac : AsmConfigExact width)
    (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (k f frame : Nat) (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat) (fragment : straightWord program = true)
    (premises : WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := target.clock + extraClock}) ≤
        StackAllocSteps.loopOnlyCost 0 compiled ∧
      StackSteps.steps (compiled, {target with clock := target.clock + extraClock}) ≤
        StackAllocSteps.loopOnlyCost 0 compiled * WordSteps.steps program source := by
  obtain ⟨extra, post, output, run, related⟩ :=
    CompCorrect.compCorrect ac program source k f frame sourcePost target result
      bs bsPost n nPost compiled lens premises
  have shape := straightWord_compiled ac program fragment (bs, n) (k, f, frame)
  rw [premises.2.2.2.2.2.1] at shape
  have bound := straightLineSteps compiled shape {target with clock := target.clock + extra}
  have positive := WordSteps.steps_pos program source
  refine ⟨extra, post, output, run, related, bound, ?_⟩
  nlinarith

end SteppedFlapjack.WordToStackSteps
