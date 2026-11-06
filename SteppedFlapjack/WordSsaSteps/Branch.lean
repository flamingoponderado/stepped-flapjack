import SteppedFlapjack.WordSsaSteps.Instruction

/-! SSA lowering of loop-free Word branches. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSimpSteps
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- SSA lowers a loop-free branch to another loop-free branch. -/
theorem ssaBranch_shape {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    ∀ ssa next targets, Branch (ssaCcTrans p ssa next targets).1 := by
  induction shape with
  | assign dst e => intro ssa next targets; simp [ssaCcTrans,nextVarRename]; exact .assign _ _
  | inst i => intro ssa next targets; exact ssaInst_branch i ssa next
  | move pri moves =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : listNextVarRename (moves.map Prod.fst) ssa next with ⟨vs,ssa',next'⟩
    exact .move _ _
  | get dst n => intro ssa next targets; simp [ssaCcTrans,nextVarRename]; exact .get _ _
  | opCurrHeap op dst src => intro ssa next targets; simp [ssaCcTrans,nextVarRename]; exact .opCurrHeap _ _ _
  | set n e => intro ssa next targets; exact .set _ _
  | store e src => intro ssa next targets; exact .store _ _
  | skip => intro ssa next targets; exact .skip
  | tick => intro ssa next targets; exact .tick
  | ret r vs => intro ssa next targets; exact .seq (.move _ _) (.ret _ _)
  | «break» n => intro ssa next targets; exact break_branch n ssa next targets
  | «continue» n => intro ssa next targets; exact continue_branch n ssa next targets
  | @seq a b ha hb iha ihb =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : ssaCcTrans a ssa next targets with ⟨a',sa,na⟩
    rcases k : ssaCcTrans b sa na targets with ⟨b',sb,nb⟩
    have aa := iha ssa next targets
    have bb := ihb sa na targets
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb
  | @ite cmp r ri a b ha hb iha ihb =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : ssaCcTrans a ssa next targets with ⟨a',sa,na⟩
    rcases k : ssaCcTrans b ssa na targets with ⟨b',sb,nb⟩
    rcases z : fixInconsistencies (mkPrio a' b') sa sb nb with ⟨ac,bc,nf,sf⟩
    have aa := iha ssa next targets
    have bb := ihb ssa na targets
    have cons := fixInconsistencies_branch (width := width) (mkPrio a' b') sa sb nb
    simp only [h] at aa
    simp only [k] at bb
    simp only [z] at cons
    exact .ite _ _ _ (.seq aa cons.1) (.seq bb cons.2)

/-- The actual SSA output of a loop-free branch has a calculable syntax-size
bound on visits, for arbitrary SSA maps and loop-target lists. -/
theorem ssaBranch_steps {p : WordLangProgHOL (BitVec width)} (shape : Branch p)
    (ssa : Spt Nat) (next : Nat) (targets : List (Spt Nat × Spt Unit × Spt Unit))
    (s : WordSemStateFiniteExact width C F) :
    steps (ssaCcTrans p ssa next targets).1 s ≤ sizeOf (ssaCcTrans p ssa next targets).1 :=
  branch_static (ssaBranch_shape shape ssa next targets) s

end SteppedFlapjack.WordSsaSteps
