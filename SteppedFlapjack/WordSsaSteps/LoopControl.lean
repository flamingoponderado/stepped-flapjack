import SteppedFlapjack.WordSsaSteps.Reconcile

/-! Quantitative shape of SSA loop-control lowering. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSimpSteps
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- SSA break code is loop-free whether or not the target loop exists. -/
theorem break_branch (index : Nat) (ssa : Spt Nat) (next : Nat)
    (targets : List (Spt Nat × Spt Unit × Spt Unit)) :
    Branch (ssaCcTrans (width := width) (.break index) ssa next targets).1 := by
  simp only [ssaCcTrans]
  cases h : targets[index]? with
  | none => exact .break index
  | some value =>
    rcases value with ⟨target,names,exits⟩
    have shape := reconcile_branch (width := width) ssa target exits
    cases hm : ssaReconcile (width := width) ssa target exits <;> simp only [hm] at shape ⊢
    all_goals first | exact .break index | exact .seq shape (.break index)

/-- SSA continue code is loop-free whether or not the target loop exists. -/
theorem continue_branch (index : Nat) (ssa : Spt Nat) (next : Nat)
    (targets : List (Spt Nat × Spt Unit × Spt Unit)) :
    Branch (ssaCcTrans (width := width) (.continue index) ssa next targets).1 := by
  simp only [ssaCcTrans]
  cases h : targets[index]? with
  | none => exact .continue index
  | some value =>
    rcases value with ⟨target,names,exits⟩
    have shape := reconcile_branch (width := width) ssa target names
    cases hm : ssaReconcile (width := width) ssa target names <;> simp only [hm] at shape ⊢
    all_goals first | exact .continue index | exact .seq shape (.continue index)

/-- Loop-control lowering visits at most the size of the generated code. -/
theorem loopControl_steps (index : Nat) (ssa : Spt Nat) (next : Nat)
    (targets : List (Spt Nat × Spt Unit × Spt Unit)) (s : WordSemStateFiniteExact width C F) :
    steps (ssaCcTrans (width := width) (.break index) ssa next targets).1 s ≤
      sizeOf (ssaCcTrans (width := width) (.break index) ssa next targets).1 ∧
    steps (ssaCcTrans (width := width) (.continue index) ssa next targets).1 s ≤
      sizeOf (ssaCcTrans (width := width) (.continue index) ssa next targets).1 :=
  ⟨branch_static (break_branch index ssa next targets) s,
    branch_static (continue_branch index ssa next targets) s⟩

end SteppedFlapjack.WordSsaSteps
