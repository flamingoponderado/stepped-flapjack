import SteppedFlapjack.WordDeadSteps.Correct
import Flapjack.Compiler.Backend.WordCse.Transform

/-! Loop-free shape of CSE's knowledge-dependent leaf rewrites. -/
namespace SteppedFlapjack.WordCseSteps
open Flapjack Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width]

theorem addToDataAux_branch (data : Knowledge) (dst : Nat) (key : List Nat)
    {original : WordLangProgHOL (BitVec width)} (shape : Branch original) :
    Branch (addToDataAux data dst key original).2 := by
  unfold addToDataAux
  split <;> split <;> first | exact .move _ _ | exact shape

theorem addToLoadAux_branch (data : Knowledge) (dst : Nat) (key : List Nat)
    {original : WordLangProgHOL (BitVec width)} (shape : Branch original) :
    Branch (addToLoadAux data dst key original).2 := by
  unfold addToLoadAux
  split <;> split <;> first | exact .move _ _ | exact shape

theorem addToData_branch {adjWidth : Nat} [NeZero adjWidth] (data : Knowledge) (dst : Nat)
    (adjusted : HolInst adjWidth) (original : HolInst width) : Branch (addToData data dst adjusted original).2 :=
  addToDataAux_branch data dst _ (.inst _)

theorem addToDataConst_branch (data : Knowledge) (dst : Nat) (value : BitVec width) :
    Branch (addToDataConst data dst value).2 := by
  unfold addToDataConst
  dsimp only
  split <;> exact .inst _

theorem getClause_branch (data : Knowledge) (dst : Nat) (name : WordStoreHOL) :
    Branch (getClause (width := width) data dst name).2 := by
  unfold getClause
  dsimp only
  split <;> split <;> first | exact .get _ _ | exact .move _ _

theorem setClause_branch (data : Knowledge) (name : WordStoreHOL) (e : WordLangExpHOL (BitVec width)) :
    Branch (setClause data name e).2 := by
  unfold setClause
  split
  · exact .set _ _
  · dsimp only
    split <;> try {exact .set _ _}
    split <;> exact .set _ _

/-- Every instruction rewritten by CSE is still one loop-free branch. -/
theorem wordCseInst_branch (data : Knowledge) (i : HolInst width) : Branch (wordCseInst data i).2 := by
  cases i with
  | skip => exact .inst _
  | const dst w =>
    simp only [wordCseInst]
    split
    · exact .inst _
    · exact addToDataConst_branch _ _ _
  | arith a =>
    simp only [wordCseInst]
    split
    · exact addToData_branch _ _ _ _
    · exact .inst _
  | mem op r addr =>
    cases addr with
    | addr a ofs =>
      simp only [wordCseInst]
      split
      · exact .inst _
      · split
        · exact .inst _
        · exact addToLoadAux_branch _ _ _ (.inst _)
  | fp op => exact .inst _

end SteppedFlapjack.WordCseSteps
