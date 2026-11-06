import SteppedFlapjack.StackRemoveSteps.EntrySteps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Defs

/-! Static run cost for an oracle that supplies no code or bitmap words. -/
namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
variable {width : Nat} [NeZero width] {C F : Type}

/-- Keep each configuration while replacing dynamically installed code and
bitmaps with empty lists. -/
def emptyInstallOracle
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    Nat → C × List (Nat × HolProg width) × List (BitVec width) :=
  fun i => ((oracle i).1,[],[])

/-- An empty-install oracle contributes no bitmap words for any prefix. -/
theorem emptyInstallOracle_bitmap (n : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    oracleBitmapBudget n (emptyInstallOracle oracle) = 0 := by
  induction n generalizing oracle with
  | zero => rfl
  | succ n ih =>
    have shift : holShiftSeq 1 (emptyInstallOracle oracle) = emptyInstallOracle (holShiftSeq 1 oracle) := by
      funext i
      rfl
    simp only [oracleBitmapBudget,emptyInstallOracle,List.length_nil,Nat.zero_add,shift,ih]

/-- An empty-install oracle contributes no candidate program cost. -/
theorem emptyInstallOracle_cost (B : Nat) (bounds : BitVec width × BitVec width) (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    oraclePrefixCost B bounds n {s with compileOracle := emptyInstallOracle s.compileOracle} = 0 := by
  have empty : ∀ xs : List Nat, xs.flatMap (fun _ => ([] : List Nat)) = [] := by
    intro xs
    induction xs <;> simp_all
  simp only [oraclePrefixCost,emptyInstallOracle,List.map_nil,empty,maxListNat]

/-- The computed cost of a run with an empty-install oracle is independent of
its source-step limit and depends only on the initial code and bitmap size. -/
theorem computedRunCost_emptyInstallOracle (bounds : BitVec width × BitVec width) (n : Nat)
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    computedRunCost bounds n program {s with compileOracle := emptyInstallOracle s.compileOracle} =
      max 1 (max (leafCost s.bitmaps.length bounds program) (codeCost s.bitmaps.length bounds s)) := by
  have hb := emptyInstallOracle_bitmap n s.compileOracle
  have ho := emptyInstallOracle_cost s.bitmaps.length bounds n s
  simp only [computedRunCost,initialBitmapBudget,hb,Nat.add_zero,initialRunCost,
    initialCodeOracleCost,ho,Nat.max_zero,codeCost]


/-- If all oracle entries contain no installable code or bitmaps, the computed
factor is the same constant for every source-step limit. -/
theorem computedRunCost_of_emptyInstallOracle (bounds : BitVec width × BitVec width) (n : Nat)
    (program : HolProg width) (s : StackSemStateFiniteExact width C F)
    (empty : ∀ i, (s.compileOracle i).2.1 = [] ∧ (s.compileOracle i).2.2 = []) :
    computedRunCost bounds n program s =
      max 1 (max (leafCost s.bitmaps.length bounds program) (codeCost s.bitmaps.length bounds s)) := by
  have oracleEq : emptyInstallOracle s.compileOracle = s.compileOracle := by
    funext i
    have h := empty i
    rcases entry : s.compileOracle i with ⟨config,code,bitmap⟩
    simp only [entry] at h
    obtain ⟨rfl,rfl⟩ := h
    simp [emptyInstallOracle,entry]
  have stateEq : {s with compileOracle := emptyInstallOracle s.compileOracle} = s := by simp [oracleEq]
  have h := computedRunCost_emptyInstallOracle bounds n program s
  rw [stateEq] at h
  exact h

end SteppedFlapjack.StackRemoveSteps.CompCorrect

namespace SteppedFlapjack.StackRemoveSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- With no installable oracle code or bitmap words, the actual Stack removal
entry simulation has a single initial-code factor independent of the step limit. -/
theorem entryWithinSteps_emptyInstallOracle {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock n : Nat)
    (source target post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) = (result, post))
    (nonError : result ≠ some .error)
    (hsteps : steps (.call none (.inl start) none, {source with clock := clock}) ≤ n)
    (empty : ∀ i, (source.compileOracle i).2.1 = [] ∧ (source.compileOracle i).2.2 = []) :
    ∃ extra postTarget, evaluate (.call none (.inl start) none, {target with clock := extra + clock}) =
        (result, postTarget) ∧ postTarget.ffi = post.ffi ∧
      steps (.call none (.inl start) none, {target with clock := extra + clock}) ≤
        max 1 (max (leafCost source.bitmaps.length bounds (.call none (.inl start) none))
          (codeCost source.bitmaps.length bounds source)) * n := by
  obtain ⟨extra,postTarget,he,hffi,hbound⟩ :=
    entryWithinSteps jump bounds pointer start clock n source target post result relation run nonError hsteps
  refine ⟨extra,postTarget,he,hffi,?_⟩
  rw [computedRunCost_of_emptyInstallOracle bounds n _ source empty] at hbound
  exact hbound


/-- Stack allocation maps an empty-install oracle to another empty-install
oracle, independently of its configuration transformation. -/
theorem stackAllocTarget_emptyInstallOracle {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width)
    (cr : Flapjack.Compiler.Backend.StackAlloc.CompCorrect.CompileFn width C)
    (config : DataToWord.Config) (source : StackSemStateFiniteExact width C F)
    (clock : Nat) (regs : HolFiniteMapExact Nat (WordLocW width))
    (empty : ∀ i, (source.compileOracle i).2.1 = [] ∧ (source.compileOracle i).2.2 = []) :
    ∀ i, ((Flapjack.Compiler.Backend.StackAlloc.CompCorrect.Tgt anything cr config source clock regs).compileOracle i).2.1 = [] ∧
      ((Flapjack.Compiler.Backend.StackAlloc.CompCorrect.Tgt anything cr config source clock regs).compileOracle i).2.2 = [] := by
  intro i
  have h := empty i
  simpa [Flapjack.Compiler.Backend.StackAlloc.CompCorrect.Tgt,
    Flapjack.Compiler.Backend.StackAlloc.CompCorrect.oracleMap] using h

/-- The factor used after Stack allocation is independent of the selected
oracle prefix when the input oracle contains no installable code or bitmaps. -/
theorem stackAllocTarget_computedRunCost_empty {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width)
    (cr : Flapjack.Compiler.Backend.StackAlloc.CompCorrect.CompileFn width C)
    (config : DataToWord.Config) (source : StackSemStateFiniteExact width C F)
    (clock : Nat) (regs : HolFiniteMapExact Nat (WordLocW width))
    (bounds : BitVec width × BitVec width) (n : Nat) (program : HolProg width)
    (empty : ∀ i, (source.compileOracle i).2.1 = [] ∧ (source.compileOracle i).2.2 = []) :
    let allocated := Flapjack.Compiler.Backend.StackAlloc.CompCorrect.Tgt anything cr config source clock regs
    computedRunCost bounds n program allocated =
      max 1 (max (leafCost source.bitmaps.length bounds program)
        (codeCost source.bitmaps.length bounds allocated)) := by
  exact computedRunCost_of_emptyInstallOracle bounds n program _
    (stackAllocTarget_emptyInstallOracle anything cr config source clock regs empty)


/-- Neither the selected source-step limit nor the input clock affects this
factor when the allocation input has an empty-install oracle. -/
theorem stackAllocTarget_computedRunCost_clock_independent
    {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width)
    (cr : Flapjack.Compiler.Backend.StackAlloc.CompCorrect.CompileFn width C)
    (config : DataToWord.Config) (source : StackSemStateFiniteExact width C F)
    (sourceClock extraClock : Nat) (regs : HolFiniteMapExact Nat (WordLocW width))
    (bounds : BitVec width × BitVec width) (n : Nat) (program : HolProg width)
    (empty : ∀ i, (source.compileOracle i).2.1 = [] ∧ (source.compileOracle i).2.2 = []) :
    let allocated := Flapjack.Compiler.Backend.StackAlloc.CompCorrect.Tgt anything cr config
      {source with clock := sourceClock} extraClock regs
    let fixed := Flapjack.Compiler.Backend.StackAlloc.CompCorrect.Tgt anything cr config
      {source with clock := 0} 0 regs
    computedRunCost bounds n program allocated =
      max 1 (max (leafCost source.bitmaps.length bounds program)
        (codeCost source.bitmaps.length bounds fixed)) := by
  have h := stackAllocTarget_computedRunCost_empty anything cr config
    {source with clock := sourceClock} extraClock regs bounds n program (by simpa using empty)
  simpa only [Flapjack.Compiler.Backend.StackAlloc.CompCorrect.Tgt,codeCost] using h

end SteppedFlapjack.StackRemoveSteps
