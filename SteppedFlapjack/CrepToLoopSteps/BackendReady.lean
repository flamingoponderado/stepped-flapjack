import SteppedFlapjack.CrepToLoopSteps.WordComposition
import SteppedFlapjack.LoopToWordSteps.RiscVComposition

/-! Bridge direct Crep programs to the supported machine backend fragment. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- Compilation lands in the shared Loop-to-RISC-V fragment. -/
theorem compile_stackReady {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : DirectProgram p)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    StackReady (compileHOLExact ctxt live p) := by
  induction shape with
  | leaf leaf => cases leaf <;> simp only [compileHOLExact] <;> exact .leaf (by constructor)
  | returnNil =>
    simp only [compileHOLExact, compileExpsHOLExact, genTemps, List.nil_append]
    exact .seq (.leaf (.ret _)) (.leaf .skip)
  | seq ha hb iha ihb => simpa only [compileHOLExact] using StackReady.seq iha ihb

/-- The source outcomes handled by the completed backend theorem. -/
inductive CompleteCrepResult : Option (CrepResultHOLExact 64) → Prop
  | return (values) : CompleteCrepResult (some (.return values))
  | ffi (event) : CompleteCrepResult (some (.finalFfi event))

/-- Completed source outcomes map to completed Loop outcomes. -/
theorem completeCrep_loop {result : Option (CrepResultHOLExact 64)}
    (complete : CompleteCrepResult result) : CompleteLoopResult (resultToLoop result) := by
  cases complete with
  | «return» values => exact .return _
  | ffi event => exact .ffi _

/-- Non-error follows from source completion. -/
theorem completeCrep_nonerror {result : Option (CrepResultHOLExact 64)}
    (complete : CompleteCrepResult result) : result ≠ some .error := by
  cases complete <;> simp

end SteppedFlapjack.CrepToLoopSteps
