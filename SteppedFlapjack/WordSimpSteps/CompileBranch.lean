import SteppedFlapjack.WordSimpSteps.HoistBranch

/-! Complete WordSimp bounds for loop-free branches. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

/-- All four stages of the real WordSimp pass preserve branch shape. -/
theorem compileExp_branch {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    Branch (compileExp p) := by
  apply pushOutIfAux_branch
  apply simpDuplicateIf_branch
  apply constFpLoop_branch
  exact seqAssoc_branch shape .skip

/-- WordSimp's actual output visits are bounded by a computed syntax factor
for every loop-free branch, independently of its runtime state. -/
theorem compileExp_branch_steps {p : WordLangProgHOL (BitVec width)} (shape : Branch p)
    (s : WordSemStateFiniteExact width C F) :
    steps (compileExp p) s ≤ sizeOf (compileExp p) * steps p s := by
  have bound := branch_static (compileExp_branch shape) s
  have positive := steps_pos p s
  nlinarith

/-- The complete actual WordSimp pass preserves branch evaluation and has a
source-relative visit bound under the standard GC-function invariant. -/
theorem compileExp_branch_correct {p : WordLangProgHOL (BitVec width)} (shape : Branch p)
    (s : WordSemStateFiniteExact width C F) (gc : gcFunConstOk s.gcFun) :
    evaluate (compileExp p) s = evaluate p s ∧
    steps (compileExp p) s ≤ sizeOf (compileExp p) * steps p s := by
  constructor
  · simp only [Compiler.Backend.WordSimp.compileExp]
    rw [evaluate_simp_push_out_if, evaluate_simp_duplicate_if _ _ gc,
      evaluate_const_fp _ _ gc, evaluate_Seq_assoc]
  · exact compileExp_branch_steps shape s

end SteppedFlapjack.WordSimpSteps
