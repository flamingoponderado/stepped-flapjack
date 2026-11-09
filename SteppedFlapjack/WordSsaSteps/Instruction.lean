import SteppedFlapjack.WordSsaSteps.LoopControl

/-! Quantitative shape of SSA instruction lowering. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSimpSteps
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Constant and skip instructions lower to loop-free SSA code. -/
theorem ssaConst_branch (dst : Nat) (value : BitVec width) (ssa : Spt Nat) (next : Nat) :
    Branch (ssaCcTransInst (.const dst value) ssa next).1 := by
  simp only [ssaCcTransInst]
  rcases h : nextVarRename dst ssa next with ⟨v,t,n⟩
  exact .inst _

/-- Constant instruction lowering has a static visit bound. -/
theorem ssaConst_steps (dst : Nat) (value : BitVec width) (ssa : Spt Nat) (next : Nat)
    (s : WordSemStateFiniteExact width C F) :
    steps (ssaCcTransInst (.const dst value) ssa next).1 s = 1 := by
  simp only [ssaCcTransInst]
  rcases h : nextVarRename dst ssa next with ⟨v,t,n⟩
  exact steps_leaf _ _ rfl

/-- SSA lowers any individual Word instruction to loop-free code. -/
theorem ssaInst_branch (i : WordLangInst (BitVec width)) (ssa : Spt Nat) (next : Nat) :
    Branch (ssaCcTransInst i ssa next).1 := by
  cases i with
  | skip => exact .skip
  | const dst value => exact ssaConst_branch dst value ssa next
  | arith a =>
    cases a <;> simp only [ssaCcTransInst,nextVarRename] <;>
      repeat' first | split | constructor
  | mem op dst addr =>
    cases op <;> cases addr <;> simp only [ssaCcTransInst,nextVarRename] <;>
      repeat' first | split | constructor

/-- The visits to the lowered instruction are bounded by its generated size. -/
theorem ssaInst_steps (i : WordLangInst (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (s : WordSemStateFiniteExact width C F) :
    steps (ssaCcTransInst i ssa next).1 s ≤ sizeOf (ssaCcTransInst i ssa next).1 :=
  branch_static (ssaInst_branch i ssa next) s

end SteppedFlapjack.WordSsaSteps
