import SteppedFlapjack.WordToStackSteps.Basic
import SteppedFlapjack.StackRemoveSteps.InitSteps

/-! Static bounds for instruction compilation and its register helpers. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackRemoveSteps

variable {width : Nat} [NeZero width]

theorem straightLine_stackLoad (loads : List (Nat × Nat)) (p : HolProg width)
    (hp : straightLine p = true) : straightLine (wStackLoadNative loads p) = true := by
  induction loads with
  | nil => exact hp
  | cons x xs ih => cases x; simp [wStackLoadNative, straightLine, ih]

theorem straightLine_regWrite1 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ r, straightLine (g r) = true) : straightLine (wRegWrite1Native g r kf) = true := by
  simp only [wRegWrite1Native]
  split <;> simp [straightLine, hg]

theorem straightLine_regWrite2 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ r, straightLine (g r) = true) : straightLine (wRegWrite2Native g r kf) = true := by
  simp only [wRegWrite2Native]
  split <;> simp [straightLine, hg]

theorem straightLine_inst (i : HolInst width) (kf : Nat × Nat × Nat) :
    straightLine (wInstNative i kf) = true := by
  cases i with
  | arith a =>
    cases a <;> try (rename_i op d s ri; cases ri)
    all_goals
      simp only [wInstNative]
      first | apply straightLine_stackLoad; apply straightLine_regWrite1; intro; rfl
            | apply straightLine_stackLoad; rfl
            | rfl
  | mem op d addr =>
    cases addr
    cases op <;> simp only [wInstNative]
    all_goals
      first | apply straightLine_stackLoad; apply straightLine_regWrite1; intro; rfl
            | apply straightLine_stackLoad; rfl
            | rfl
  | fp f =>
    cases f <;> simp only [wInstNative]
    all_goals
      first | apply straightLine_regWrite1; intro; rfl
            | split <;> first | apply straightLine_regWrite1; intro; rfl
                              | apply straightLine_regWrite2; intro; apply straightLine_regWrite1; intro; rfl
            | apply straightLine_stackLoad; rfl
            | rfl
  | skip => rfl
  | const n c => simp only [wInstNative]; apply straightLine_regWrite1; intro; rfl

/-- Scheduled register moves contain only straight-line stack operations. -/
theorem straightLine_moveSingle (xy : Sum Nat Nat × Sum Nat Nat) (kf : Nat × Nat × Nat) :
    straightLine (wMoveSingleNative (width := width) xy kf) = true := by
  rcases xy with ⟨x, y⟩
  cases x <;> cases y <;> rfl

theorem straightLine_moveAux (moves : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    straightLine (wMoveAuxNative (width := width) moves kf) = true := by
  induction moves with
  | nil => rfl
  | cons xy rest ih =>
    cases rest with
    | nil => exact straightLine_moveSingle xy kf
    | cons a as => simp only [wMoveAuxNative, straightLine, Bool.and_eq_true]; exact ⟨straightLine_moveSingle xy kf, ih⟩

theorem straightLine_move (moves : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    straightLine (wMoveNative (width := width) moves kf) = true := by
  exact straightLine_moveAux _ kf

/-- Compiling any WordSem machine instruction produces straight-line StackSem code. -/
theorem straightLine_compileInst (ac : AsmConfigExact width) (i : WordLangInst (BitVec width))
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    straightLine (compNative ac false (.inst i) bs kf).1 = true := by
  simp only [compNative]
  exact straightLine_inst (HolInst.ofWordLangInst i) kf


/-- An instruction run is simulated by compiled StackSem code within a
structural bound determined by the compiled instruction and register layout. -/
theorem inst_simulation {C F : Type} (ac : AsmConfigExact width)
    (instruction : WordLangInst (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (k f frame : Nat) (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.inst instruction) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.inst instruction) = true ∧ flatExpConventions (.inst instruction) = true ∧
      compNative ac false (.inst instruction) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.inst instruction) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := target.clock + extraClock}) ≤
        StackAllocSteps.loopOnlyCost 0 compiled * WordSteps.steps (.inst instruction) source := by
  obtain ⟨extra, post, output, run, related⟩ :=
    CompCorrect.compCorrect ac (.inst instruction) source k f frame sourcePost target result
      bs bsPost n nPost compiled lens premises
  refine ⟨extra, post, output, run, related, ?_⟩
  have shape := straightLine_compileInst ac instruction (bs, n) (k, f, frame)
  rw [premises.2.2.2.2.2.1] at shape
  have bound := straightLineSteps compiled shape {target with clock := target.clock + extra}
  have sourceCount : WordSteps.steps (.inst instruction) source = 1 := by
    apply WordSteps.steps_leaf
    rfl
  simpa [sourceCount] using bound

end SteppedFlapjack.WordToStackSteps
