import SteppedFlapjack.WordTwoRegSteps.Correct
import SteppedFlapjack.WordCopySteps.TailEntry

/-! Optional register rewriting for tail entries. -/
namespace SteppedFlapjack.WordTwoRegSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordInst
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordDeadSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

/-- The register rewrite keeps branch shape and allowed direct destinations. -/
theorem threeToTwo_allowedTailEntry {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) : AllowedTailEntry allowed (threeToTwoReg p) := by
  induction shape with
  | branch h => exact .branch (threeToTwo_branch h)
  | call loc good => exact .call loc good
  | seq _ _ a b => exact .seq a b

/-- The actual optional rewrite preserves a non-error execution, destination
bounds, and an output syntax/clock visit bound. -/
theorem threeToTwo_tailEntry_correct {C F : Type} (flag : Bool)
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error)
    (distinct : everyInst distinctTarReg p = true) :
    evaluate (threeToTwoRegProg flag p) s = (res,post) ∧
    WordTailEntryShape (threeToTwoRegProg flag p) ∧ TailEntryCodeBound (threeToTwoRegProg flag p) s.code K ∧
    WordSteps.steps (threeToTwoRegProg flag p) s ≤ sizeOf (threeToTwoRegProg flag p) * (K+1) * (s.clock+1) := by
  have init := tailEntry_allowed_of_code shape s.code K code
  have out : AllowedTailEntry (fun loc => ∃ callee, sptLookup loc s.code = some (1,callee) ∧
      LoopSequence callee ∧ sizeOf callee ≤ K) (threeToTwoRegProg flag p) := by
    cases flag with
    | false => exact init
    | true => exact threeToTwo_allowedTailEntry init
  have outShape := allowedTailEntry_shape out
  have outCode := allowedTailEntry_calls out
  exact ⟨evaluate_three_to_two_reg_prog p s res post flag ⟨run,nonerror,distinct⟩,outShape,outCode,
    tailEntry_clock_bound outShape s K (tailEntry_noInstall outShape) noInstallCode outCode⟩

end SteppedFlapjack.WordTwoRegSteps
