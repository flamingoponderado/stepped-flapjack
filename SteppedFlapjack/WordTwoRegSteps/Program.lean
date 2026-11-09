import SteppedFlapjack.WordCopySteps.Correct
import Flapjack.Compiler.Backend.WordInst.Proofs.ThreeToTwo

/-! Quantitative three-to-two register rewriting. -/
namespace SteppedFlapjack.WordTwoRegSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordInst SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- The register rewrite preserves the supported branch fragment. -/
theorem threeToTwo_branch {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    Branch (threeToTwoReg p) := by
  induction shape with
  | assign dst e => exact .assign _ _
  | store e src => exact .store _ _
  | skip => exact .skip
  | tick => exact .tick
  | ret r vs => exact .ret _ _
  | «break» n => exact .break _
  | «continue» n => exact .continue _
  | move pri ms => exact .move _ _
  | get dst n => exact .get _ _
  | set n e => exact .set _ _
  | opCurrHeap op dst src => exact .seq (.move _ _) (.opCurrHeap _ _ _)
  | inst i =>
    cases i with
    | arith a => cases a <;> simp only [threeToTwoReg] <;> first | exact .inst _ | exact .seq (.move _ _) (.inst _)
    | skip => exact .inst _
    | const dst value => exact .inst _
    | mem op dst addr => exact .inst _
  | seq ha hb iha ihb => exact .seq iha ihb
  | ite cmp r ri ha hb iha ihb => exact .ite cmp r ri iha ihb

/-- Three-to-two rewriting preserves recursive call-free programs. -/
theorem threeToTwo_loopSequence {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    LoopSequence (threeToTwoReg p) := by
  induction shape with
  | branch hp => exact .branch (threeToTwo_branch hp)
  | loop names exits hp => exact .loop names exits (threeToTwo_branch hp)
  | seq ha hb iha ihb => exact .seq iha ihb
  | nestedLoop names exits hp ih => exact .nestedLoop names exits ih
  | conditional cmp r ri ha hb iha ihb => exact .conditional cmp r ri iha ihb

/-- The optional rewrite preserves a non-error execution and has an output
visit bound under its standard distinct-target-register convention. -/
theorem threeToTwo_correct_with_steps (flag : Bool) {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error)
    (distinct : everyInst distinctTarReg p = true) :
    evaluate (threeToTwoRegProg flag p) s = (res,post) ∧
    steps (threeToTwoRegProg flag p) s ≤ sizeOf (threeToTwoRegProg flag p) * (s.clock+1) := by
  constructor
  · exact evaluate_three_to_two_reg_prog p s res post flag ⟨run,nonerror,distinct⟩
  · cases flag with
    | false => exact loopSequence_clock_bound shape s
    | true => exact loopSequence_clock_bound (threeToTwo_loopSequence shape) s

end SteppedFlapjack.WordTwoRegSteps
