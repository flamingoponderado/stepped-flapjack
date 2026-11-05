import SteppedFlapjack.WordToStackSteps.StraightLine

/-! Structural target bounds for call-free WordSem programs with loops. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackRemoveSteps SteppedFlapjack.StackAllocSteps
variable {width : Nat} [NeZero width]

/-- Straight-line operations closed under nesting, conditionals and loops. -/
def loopWord : WordLangProgHOL (BitVec width) → Bool
  | .seq a b | .ite _ _ _ a b => loopWord a && loopWord b
  | .loop _ a _ | .mustTerminate a => loopWord a
  | p => straightWord p

theorem loopOnly_stackLoad (loads : List (Nat × Nat)) (p : HolProg width)
    (hp : loopOnly p = true) : loopOnly (wStackLoadNative loads p) = true := by
  induction loads with
  | nil => exact hp
  | cons x xs ih => cases x; simp [wStackLoadNative, loopOnly, ih]

/-- Compilation of the call-free loop fragment cannot introduce calls. -/
theorem loopWord_compiled (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (hp : loopWord p = true) (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    loopOnly (compNative ac false p bs kf).1 = true := by
  by_cases hs : straightWord p = true
  · exact straightLineLoopOnly _ (straightWord_compiled ac p hs bs kf)
  cases h : p <;> simp_all only [loopWord, straightWord, Bool.and_eq_true, Bool.false_eq_true,
    Bool.not_eq_true]
  case mustTerminate q =>
    simp only [compNative]
    exact loopWord_compiled ac q hp bs kf
  case seq a b =>
    simp only [compNative]
    rcases hc : compNative ac false a bs kf with ⟨ca, bs1⟩
    rcases hd : compNative ac false b bs1 kf with ⟨cb, bs2⟩
    simp only [loopOnly, Bool.and_eq_true]
    constructor
    · simpa only [hc] using loopWord_compiled ac a hp.1 bs kf
    · simpa only [hd] using loopWord_compiled ac b hp.2 bs1 kf
  case ite cmp r ri a b =>
    simp only [compNative]
    rcases hc : compNative ac false a bs kf with ⟨ca, bs1⟩
    rcases hd : compNative ac false b bs1 kf with ⟨cb, bs2⟩
    have ha : loopOnly ca = true := by simpa only [hc] using loopWord_compiled ac a hp.1 bs kf
    have hb : loopOnly cb = true := by simpa only [hd] using loopWord_compiled ac b hp.2 bs1 kf
    cases ri with
    | reg n => simp only; apply loopOnly_stackLoad; simp [loopOnly, ha, hb]
    | imm i =>
      simp only
      split <;> simp [loopOnly, loopOnly_stackLoad, ha, hb]
  case loop names body exitNames =>
    simp only [compNative]
    rcases hc : compNative ac false body bs kf with ⟨compiled, bs1⟩
    simp only [loopOnly]
    simpa only [hc] using loopWord_compiled ac body hp bs kf
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf <;> omega

/-- Any given target execution of the compiled call-free loop fragment is
bounded by a computable structural cost at its actual initial target clock. -/
theorem loopWord_target_bound {C F : Type} (ac : AsmConfigExact width)
    (program : WordLangProgHOL (BitVec width)) (fragment : loopWord program = true)
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (target : StackSemStateFiniteExact width C F) :
    StackSteps.steps ((compNative ac false program bs kf).1, target) ≤
      loopOnlyCost target.clock (compNative ac false program bs kf).1 :=
  loopOnlyCostBound target.clock _ (loopWord_compiled ac program fragment bs kf) target (Nat.le_refl _)


/-- On related states, the actual compiled target run has a bound using the
source clock. This is a structural target bound, not yet the simulation of
source outcomes for loops. -/
theorem loopWord_related_bound {C F : Type} (ac : AsmConfigExact width)
    (program : WordLangProgHOL (BitVec width)) (fragment : loopWord program = true)
    (bs : AppList (BitVec width) × Nat) (k f frame : Nat) (lens : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (related : stateRel ac k f frame source target lens 0) :
    StackSteps.steps ((compNative ac false program bs (k, f, frame)).1, target) ≤
      loopOnlyCost source.clock (compNative ac false program bs (k, f, frame)).1 := by
  have clocks : source.clock = target.clock := related.1
  rw [clocks]
  exact loopWord_target_bound ac program fragment bs (k, f, frame) target

end SteppedFlapjack.WordToStackSteps
