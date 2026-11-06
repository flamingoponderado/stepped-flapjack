import SteppedFlapjack.StackRemoveSteps.RunBudget

/-! Monotonicity of finite bitmap and oracle budgets. -/
namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackRemoveSteps
variable {width : Nat} [NeZero width]

/-- A larger bitmap budget cannot reduce a compiled leaf expansion bound. -/
theorem rawLeafCost_mono (bounds : BitVec width × BitVec width) (program : HolProg width)
    {first second : Nat} (h : first ≤ second) :
    rawLeafCost first bounds program ≤ rawLeafCost second bounds program := by
  cases hp : program <;> try simp only [rawLeafCost]
  case seq a b => exact max_le_max (rawLeafCost_mono bounds a h) (rawLeafCost_mono bounds b h)
  case ite cmp r ri a b => exact max_le_max (rawLeafCost_mono bounds a h) (rawLeafCost_mono bounds b h)
  case loop body => exact rawLeafCost_mono bounds body h
  case call ret dest handler =>
    cases ret with
    | none =>
      cases handler with
      | none => rfl
      | some v =>
        rcases v with ⟨body,l1,l2⟩
        exact max_le_max (le_refl 1) (max_le_max (le_refl 0) (rawLeafCost_mono bounds body h))
    | some r =>
      rcases r with ⟨body,l1,l2,l3⟩
      cases handler with
      | none => exact max_le_max (le_refl 1) (max_le_max (rawLeafCost_mono bounds body h) (le_refl 0))
      | some v =>
        rcases v with ⟨hbody,l1,l2⟩
        exact max_le_max (le_refl 1) (max_le_max (rawLeafCost_mono bounds body h) (rawLeafCost_mono bounds hbody h))
  case storeConsts a b c =>
    unfold storeConstsSteps copyLoopSteps
    gcongr
  all_goals rfl
termination_by sizeOf program
decreasing_by all_goals subst program; simp_wf; try omega

/-- The positive program factor is monotone in its bitmap budget. -/
theorem leafCost_mono (bounds : BitVec width × BitVec width) (program : HolProg width)
    {first second : Nat} (h : first ≤ second) :
    leafCost first bounds program ≤ leafCost second bounds program := by
  exact max_le_max (le_refl 1) (rawLeafCost_mono bounds program h)

private theorem maxListNat_le_of_forall (xs : List Nat) (k : Nat)
    (h : ∀ x ∈ xs, x ≤ k) : maxListNat xs ≤ k := by
  induction xs with
  | nil => simp [maxListNat]
  | cons y ys ih =>
    simp only [maxListNat]
    exact max_le (h y (by simp)) (ih (by intro x hx; exact h x (by simp [hx])))

/-- The initial code factor is monotone in its bitmap budget. -/
theorem codeCost_mono {C F : Type} (bounds : BitVec width × BitVec width)
    (s : StackSemStateFiniteExact width C F) {first second : Nat} (h : first ≤ second) :
    codeCost first bounds s ≤ codeCost second bounds s := by
  apply maxListNat_le_of_forall
  intro cost member
  obtain ⟨entry,entryMem,rfl⟩ := List.mem_map.mp member
  apply (leafCost_mono bounds entry.2 h).trans
  apply le_maxListNat_of_mem
  exact List.mem_map.mpr ⟨entry,entryMem,rfl⟩

/-- A larger bitmap budget and longer oracle prefix can only increase its
finite code factor. -/
theorem oraclePrefixCost_mono {C F : Type} (bounds : BitVec width × BitVec width)
    (s : StackSemStateFiniteExact width C F) {firstBudget secondBudget firstCount secondCount : Nat}
    (budget : firstBudget ≤ secondBudget) (count : firstCount ≤ secondCount) :
    oraclePrefixCost firstBudget bounds firstCount s ≤ oraclePrefixCost secondBudget bounds secondCount s := by
  apply maxListNat_le_of_forall
  intro cost member
  obtain ⟨index,indexMem,costMem⟩ := List.mem_flatMap.mp member
  obtain ⟨entry,entryMem,rfl⟩ := List.mem_map.mp costMem
  apply (leafCost_mono bounds entry.2 budget).trans
  apply le_maxListNat_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨index,List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp indexMem) count),?_⟩
  exact List.mem_map.mpr ⟨entry,entryMem,rfl⟩

/-- The oracle bitmap budget grows with the number of permitted installations. -/
theorem initialBitmapBudget_mono {C F : Type} (s : StackSemStateFiniteExact width C F)
    {first second : Nat} (h : first ≤ second) : initialBitmapBudget first s ≤ initialBitmapBudget second s := by
  unfold initialBitmapBudget
  exact Nat.add_le_add_left (oracleBitmapBudget_mono s.compileOracle h) _

/-- The complete finite-prefix Stack removal factor grows with the source
step budget. -/
theorem computedRunCost_mono {C F : Type} (bounds : BitVec width × BitVec width)
    (program : HolProg width) (s : StackSemStateFiniteExact width C F)
    {first second : Nat} (h : first ≤ second) :
    computedRunCost bounds first program s ≤ computedRunCost bounds second program s := by
  have budget := initialBitmapBudget_mono s h
  unfold computedRunCost initialRunCost initialCodeOracleCost
  exact max_le_max (le_refl 1) (max_le_max (leafCost_mono bounds program budget)
    (max_le_max (codeCost_mono bounds s budget) (oraclePrefixCost_mono bounds s budget h)))

/-- The finite-prefix cost depends on code, bitmaps and oracle, not the
execution clock of the state. -/
theorem computedRunCost_clock {C F : Type} (bounds : BitVec width × BitVec width)
    (n : Nat) (program : HolProg width) (s : StackSemStateFiniteExact width C F) (clock : Nat) :
    computedRunCost bounds n program {s with clock := clock} = computedRunCost bounds n program s := by
  rfl

end SteppedFlapjack.StackRemoveSteps.CompCorrect
