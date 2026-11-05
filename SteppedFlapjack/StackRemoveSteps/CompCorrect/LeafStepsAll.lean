import SteppedFlapjack.StackRemoveSteps.CompCorrect.Call

/-! A single step bound covering every non-recursive `HolProg` constructor
(stepped-flapjack#2, phase C3).

The induction's leaf dispatch needs `steps (comp ... p, t) <= leafCost B bounds p`
for all 28 leaves at once. The identity leaves take one step; `get`/`set` compile
to a conditional on the store name with a one-step program in each branch;
`opCurrHeap` and `dataBufferWrite` compile to one instruction; the eight
expansions are bounded in `LeafSteps`; `storeConsts` comes from the code-supplied
bound. The six recursive constructors are excluded by `hp`. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem steps_comp_leaf_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer B : Nat) (program : HolProg width) (t : StackSemStateFiniteExact width C F)
    (_bitmap : bitmapBound (width := width) (C := C) (F := F) B)
    (storeConstsBound : ∀ (temporary bitmap : Nat) (stub : Option Nat)
      (source target : StackSemStateFiniteExact width C F),
      stateRelHOL jump bounds pointer source target →
      steps (comp jump bounds pointer (.storeConsts temporary bitmap stub), target) ≤
        leafCost B bounds (.storeConsts temporary bitmap stub))
    (source : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source t)
    (hp : isRecursive program = false) :
    steps (comp jump bounds pointer program, t) ≤ leafCost B bounds program := by
  cases program with
  | seq a b => exact absurd hp (by simp [isRecursive])
  | ite cmp r ri a b => exact absurd hp (by simp [isRecursive])
  | loop body => exact absurd hp (by simp [isRecursive])
  | jumpLower l r d => exact absurd hp (by simp [isRecursive])
  | rawCall d => exact absurd hp (by simp [isRecursive])
  | call r d h => exact absurd hp (by simp [isRecursive])
  | skip =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.skip : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | inst i =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.inst i : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | alloc n =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.alloc n : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | raise n =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.raise n : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | ret n =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.ret n : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | «break» n =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.break n : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | «continue» n =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.continue n : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | ffi fn cfg cfgLen arr arrLen retAddr =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans
      (le_of_eq (steps_leaf (.ffi fn cfg cfgLen arr arrLen retAddr : HolProg width) t
        (by simp [isRecursive]))) (le_max_left _ _)
  | tick =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.tick : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | locValue dest label entry =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans
      (le_of_eq (steps_leaf (.locValue dest label entry : HolProg width) t
        (by simp [isRecursive]))) (le_max_left _ _)
  | install cb cbLen db dbLen retAddr =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans
      (le_of_eq (steps_leaf (.install cb cbLen db dbLen retAddr : HolProg width) t
        (by simp [isRecursive]))) (le_max_left _ _)
  | shMemOp op reg addr =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans
      (le_of_eq (steps_leaf (.shMemOp op reg addr : HolProg width) t
        (by simp [isRecursive]))) (le_max_left _ _)
  | codeBufferWrite addr value =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans
      (le_of_eq (steps_leaf (.codeBufferWrite addr value : HolProg width) t
        (by simp [isRecursive]))) (le_max_left _ _)
  | halt reg =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans (le_of_eq (steps_leaf (.halt reg : HolProg width) t (by simp [isRecursive])))
      (le_max_left _ _)
  | get register name =>
    simp only [comp, leafCost, rawLeafCost]
    by_cases h : name = .currHeap
    · rw [if_pos h]
      exact le_trans
        (le_of_eq (steps_leaf (moveInst register (pointer + 2)) t (by simp [isRecursive, moveInst, moveHOL])))
        (le_max_left _ _)
    · rw [if_neg h]
      exact le_trans
        (le_of_eq (steps_leaf
          (.inst (.mem .load register (.addr (pointer + 1) (storeOffset name))) : HolProg width) t
          (by simp [isRecursive])))
        (le_max_left _ _)
  | «set» name register =>
    simp only [comp, leafCost, rawLeafCost]
    by_cases h : name = .currHeap
    · rw [if_pos h]
      exact le_trans
        (le_of_eq (steps_leaf (moveInst (pointer + 2) register) t (by simp [isRecursive, moveInst, moveHOL])))
        (le_max_left _ _)
    · rw [if_neg h]
      exact le_trans
        (le_of_eq (steps_leaf
          (.inst (.mem .store register (.addr (pointer + 1) (storeOffset name))) : HolProg width) t
          (by simp [isRecursive])))
        (le_max_left _ _)
  | opCurrHeap op dest src =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans
      (le_of_eq (steps_leaf
        (.inst (.arith (.binop op dest src (.reg (pointer + 2)))) : HolProg width) t
        (by simp [isRecursive])))
      (le_max_left _ _)
  | dataBufferWrite addr value =>
    simp only [comp, leafCost, rawLeafCost]
    exact le_trans
      (le_of_eq (steps_leaf
        (.inst (.mem .store value (.addr addr 0)) : HolProg width) t
        (by simp [isRecursive])))
      (le_max_left _ _)
  | stackFree n => exact steps_comp_stackFree_le _ _ _ _ _ t
  | stackAlloc n =>
    exact steps_comp_stackAlloc_le _ _ _ _ _ t
      relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | stackStore register n => exact steps_comp_stackStore_le _ _ _ _ _ _ t
  | stackLoad register n => exact steps_comp_stackLoad_le _ _ _ _ _ _ t
  | stackGetSize register => exact steps_comp_stackGetSize_le _ _ _ _ _ t
  | stackSetSize register => exact steps_comp_stackSetSize_le _ _ _ _ _ t
  | stackLoadAny register index =>
    exact steps_comp_stackLoadAny_le _ _ _ _ _ _ t
  | stackStoreAny register index =>
    exact steps_comp_stackStoreAny_le _ _ _ _ _ _ t
  | bitmapLoad destination address =>
    exact steps_comp_bitmapLoad_le _ _ _ _ _ _ t
  | storeConsts source bitmap stub => exact storeConstsBound source bitmap stub _ _ relation

end SteppedFlapjack.StackRemoveSteps.CompCorrect
