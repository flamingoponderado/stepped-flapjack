import SteppedFlapjack.StackRemoveSteps.LeafCostBounds

/-! Leaf-cost bounds for the `call` constructor's subprograms
(stepped-flapjack#2, phase C3).

`rawLeafCost`'s `.call` arm matches on `ret` and `handler`, so the equation
compiler does not expose a rewrite lemma that unfolds it at a variable program.
Unfolding it in a file that imports the definition works, so the two bounds live
here rather than next to the others in `LeafCostBounds.lean`. -/

namespace SteppedFlapjack.StackRemoveSteps

open Flapjack Flapjack.Compiler.Backend.StackLang

variable {width : Nat} [NeZero width]

theorem callLeafCostReturn (B : Nat) (bounds : BitVec width × BitVec width)
    (body : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) :
    leafCost B bounds body ≤ leafCost B bounds (.call (some (body, link, l1, l2)) dest handler) := by
  cases handler with
  | none => simp only [leafCost, rawLeafCost]; omega
  | some h => rcases h with ⟨hb, hl, hl2⟩; simp only [leafCost, rawLeafCost]; omega

theorem callLeafCostHandler (B : Nat) (bounds : BitVec width × BitVec width)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (body : HolProg width) (hl1 hl2 : Nat) :
    leafCost B bounds body ≤ leafCost B bounds (.call ret dest (some (body, hl1, hl2))) := by
  cases ret with
  | none => simp only [leafCost, rawLeafCost]; omega
  | some r => rcases r with ⟨rb, rl, rl1, rl2⟩; simp only [leafCost, rawLeafCost]; omega

end SteppedFlapjack.StackRemoveSteps
