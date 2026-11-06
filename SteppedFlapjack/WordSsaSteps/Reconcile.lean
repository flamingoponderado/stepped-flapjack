import SteppedFlapjack.WordSimpSteps.LoopSequenceBound
import Flapjack.Compiler.Backend.WordAlloc.FullSSA

/-! Quantitative shape of SSA reconciliation and setup code. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSimpSteps
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Loop reconciliation emits either a skip or one move. -/
theorem reconcile_branch {β : Type} (cur target : Spt Nat) (names : Spt β) :
    Branch (ssaReconcile (width := width) cur target names) := by
  unfold ssaReconcile
  dsimp only
  split <;> first | exact .skip | exact .move _ _

/-- Loop reconciliation visits exactly one Word evaluator node. -/
theorem reconcile_steps {β : Type} (cur target : Spt Nat) (names : Spt β)
    (s : WordSemStateFiniteExact width C F) :
    steps (ssaReconcile (width := width) cur target names) s = 1 := by
  unfold ssaReconcile
  dsimp only
  split <;> exact steps_leaf _ _ rfl

/-- Fake reconciliation moves stay loop-free on both sides. -/
theorem fakeMoves_branch (prio : Option (Unit ⊕ Unit)) (xs : List Nat) :
    ∀ l r n, Branch (fakeMoves (width := width) prio xs l r n).1 ∧
      Branch (fakeMoves (width := width) prio xs l r n).2.1 := by
  induction xs with
  | nil => intro l r n; exact ⟨.skip,.skip⟩
  | cons x xs ih =>
    intro l r n
    simp only [fakeMoves]
    rcases h : fakeMoves prio xs l r n with ⟨a,b,n',l',r'⟩
    have shapes := ih l r n
    rw [h] at shapes
    simp only at shapes
    cases hl : sptLookup x l' <;> cases hr : sptLookup x r' <;> simp only
    · exact shapes
    · exact ⟨.seq shapes.1 (.inst _),.seq shapes.2 (.move _ _)⟩
    · exact ⟨.seq shapes.1 (.move _ _),.seq shapes.2 (.inst _)⟩
    · exact shapes

/-- Reconciliation on the two arms of an SSA conditional is loop-free. -/
theorem fixInconsistencies_branch (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (n : Nat) :
    Branch (fixInconsistencies (width := width) prio l r n).1 ∧
      Branch (fixInconsistencies (width := width) prio l r n).2.1 := by
  unfold fixInconsistencies
  dsimp only
  rcases h : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r n with ⟨lm,rm,n',l',r'⟩
  rcases k : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst) l' r' n' with ⟨a,b,n'',l'',r''⟩
  have shapes := fakeMoves_branch (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst) l' r' n'
  rw [k] at shapes
  exact ⟨.seq (.move _ _) shapes.1,.seq (.move _ _) shapes.2⟩

/-- Both conditional reconciliation programs have static syntax-size visit
bounds for arbitrary runtime states. -/
theorem fixInconsistencies_steps (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (n : Nat)
    (s : WordSemStateFiniteExact width C F) :
    steps (fixInconsistencies (width := width) prio l r n).1 s ≤
      sizeOf (fixInconsistencies (width := width) prio l r n).1 ∧
    steps (fixInconsistencies (width := width) prio l r n).2.1 s ≤
      sizeOf (fixInconsistencies (width := width) prio l r n).2.1 := by
  have shape := fixInconsistencies_branch (width := width) prio l r n
  exact ⟨branch_static shape.1 s,branch_static shape.2 s⟩

/-- The fresh-register initialization list is straight-line. -/
theorem fakeMoveList_branch (xs : List Nat) :
    Branch (xs.foldr (fun x p => .seq (fakeMove (width := width) x) p) .skip) := by
  induction xs with
  | nil => exact .skip
  | cons x xs ih => exact .seq (.inst _) ih

/-- The SSA refresh helper emits a single move. -/
theorem listNextVarRenameMove_branch (ssa : Spt Nat) (n : Nat) (xs : List Nat) :
    Branch (listNextVarRenameMove (width := width) ssa n xs).1 := by
  unfold listNextVarRenameMove
  rcases h : listNextVarRename xs ssa n with ⟨a,b,c⟩
  exact .move _ _

/-- SSA loop-entry setup consists entirely of generated branch code. -/
theorem loopSetup_branch (names exits : Spt Unit) (ssa : Spt Nat) (n : Nat) :
    Branch (loopSetup (width := width) names exits ssa n).1 := by
  unfold loopSetup
  dsimp only
  rcases h : listNextVarRename
      (((sptToAList (sptUnion names exits)).map Prod.fst).filter fun v => (sptLookup v ssa).isNone) ssa n with ⟨fresh,ext,next⟩
  rcases k : listNextVarRenameMove (width := width) ext next
      (((sptToAList (sptUnion names exits)).map Prod.fst).filter fun v => (sptLookup v ssa).isSome) with ⟨mov,ren,fin⟩
  have hm := listNextVarRenameMove_branch (width := width) ext next
      (((sptToAList (sptUnion names exits)).map Prod.fst).filter fun v => (sptLookup v ssa).isSome)
  rw [k] at hm
  apply Branch.seq
  · simpa only [List.foldr_map] using (fakeMoveList_branch (width := width) fresh)
  · exact hm

/-- Loop setup visits are statically bounded by the actual generated syntax. -/
theorem loopSetup_steps (names exits : Spt Unit) (ssa : Spt Nat) (n : Nat)
    (s : WordSemStateFiniteExact width C F) :
    steps (loopSetup (width := width) names exits ssa n).1 s ≤
      sizeOf (loopSetup (width := width) names exits ssa n).1 :=
  branch_static (loopSetup_branch (width := width) names exits ssa n) s

end SteppedFlapjack.WordSsaSteps
