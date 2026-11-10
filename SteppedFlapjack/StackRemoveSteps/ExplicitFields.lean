import SteppedFlapjack.StackRemoveSteps.OraclePrefix
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitAny

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
variable {width : Nat} [NeZero width] {C F : Type}

/-- The finite code-and-oracle factor calculated from explicit compiler inputs. -/
def costFromFields (bounds : BitVec width × BitVec width) (n : Nat) (p : HolProg width)
    (code : Spt (HolProg width)) (bitmaps : List (BitVec width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) : Nat :=
  let budget := bitmaps.length + oracleBitmapBudget n oracle
  max 1 (max (leafCost budget bounds p) (max
    (maxListNat ((sptToAList code).map fun e => leafCost budget bounds e.2))
    (maxListNat ((List.range n).flatMap fun index =>
      ((oracle index).2.1.map fun e => leafCost budget bounds e.2)))))

/-- The code-and-oracle factor depends only on those input fields. -/
theorem costFromFields_eq (bounds : BitVec width × BitVec width) (n : Nat)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    computedRunCost bounds n p s = costFromFields bounds n p s.code s.bitmaps s.compileOracle := by
  rfl

/-- Either initializer branch is bounded by the same explicit field calculation. -/
theorem makeInitAny_cost_bounded (gc jump : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (bounds : BitVec width × BitVec width) (pointer : Nat) (code : Spt (HolProg width))
    (s : StackSemStateFiniteExact width C F) (n : Nat) (p : HolProg width) :
    computedRunCost bounds n p (InitMake.makeInitAny gc maxHeap bitmaps dataSpace oracle jump bounds pointer code s) ≤
      max (costFromFields bounds n p code bitmaps oracle) (costFromFields bounds n p code [4] oracle) := by
  rw [costFromFields_eq,InitAny.makeInitAnyCode,InitAny.makeInitAnyCompileOracle,InitAny.makeInitAnyBitmaps]
  split <;> simp
/-- An oracle that installs no code or bitmap words has a constant cost
factor, regardless of the source visit limit. -/
theorem costFromFields_emptyOracle (bounds : BitVec width × BitVec width) (n : Nat)
    (p : HolProg width) (code : Spt (HolProg width)) (bitmaps : List (BitVec width)) (c : C) :
    costFromFields bounds n p code bitmaps (fun _ => (c,[],[])) =
      costFromFields bounds 0 p code bitmaps (fun _ => (c,[],[])) := by
  have budget (k : Nat) : oracleBitmapBudget k (fun _ : Nat => (c,([] : List (Nat × HolProg width)),([] : List (BitVec width)))) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have shift : holShiftSeq 1 (fun _ : Nat => (c,([] : List (Nat × HolProg width)),([] : List (BitVec width)))) =
          (fun _ : Nat => (c,([] : List (Nat × HolProg width)),([] : List (BitVec width)))) := by funext i; rfl
      simp only [oracleBitmapBudget,shift,List.length_nil,Nat.zero_add,ih]
  have empty (xs : List Nat) : xs.flatMap (fun _ => ([] : List Nat)) = [] := by
    induction xs <;> simp_all
  simp only [costFromFields,budget,Nat.add_zero,List.map_nil,empty,maxListNat]

end SteppedFlapjack.StackRemoveSteps.CompCorrect
