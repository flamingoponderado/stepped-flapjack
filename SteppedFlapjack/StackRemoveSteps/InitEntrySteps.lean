import SteppedFlapjack.StackRemoveSteps.InitSteps
import SteppedFlapjack.StackRemoveSteps.EntrySteps
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics
namespace SteppedFlapjack.StackRemoveSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- The actual stack-removal initializer and compiled entry run have a
computable combined step bound under the original initialization conditions. -/
theorem initEntryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (gen : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace pointer start : Nat)
    (s source : StackSemStateFiniteExact width C F) (jump : Bool) (bounds : BitVec width × BitVec width)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) (code : Spt (HolProg width))
    (hyp : InitMake.initPre gen maxHeap bitmaps dataSpace pointer start s ∧
      s.compileOracle = (fun index => let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      codeRelHOL jump bounds pointer code s.code)
    (opt : InitMake.makeInitOpt gen maxHeap bitmaps dataSpace oracle jump bounds pointer code s = some source)
    (k n : Nat) (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : evaluate (.call none (.inl start) none, {source with clock := k}) = (result, post))
    (nonError : result ≠ some .error)
    (hsteps : steps (.call none (.inl start) none, {source with clock := k}) ≤ n) :
    ∃ extra targetPost,
      evaluate (.call none (.inl 0) none, {s with clock := (extra + k) + 1}) = (result, targetPost) ∧
      targetPost.ffi = post.ffi ∧
      steps (.call none (.inl 0) none, {s with clock := (extra + k) + 1}) ≤
        2 + loopOnlyCost 0 (initCode gen maxHeap pointer : HolProg width) +
          computedRunCost bounds n (.call none (.inl start) none) source * n := by
  have initCorrect := InitSemantics.evaluateInitCode gen maxHeap bitmaps dataSpace pointer start s jump bounds oracle code hyp
  rcases initRun : evaluate (initCode gen maxHeap pointer, s) with ⟨ir, middle⟩
  rw [initRun] at initCorrect
  cases ir with
  | some x => exact False.elim initCorrect
  | none =>
    obtain ⟨source', opt', relation, _⟩ := initCorrect
    have same : source' = source := Option.some.inj (opt'.symm.trans opt)
    subst source'
    obtain ⟨extra, targetPost, targetRun, ffi, cost⟩ :=
      entryWithinSteps jump bounds pointer start k n source middle post result relation run nonError hsteps
    have initClock := InitClock.evaluateInitCodeClock gen maxHeap pointer s middle none (extra + k) initRun
    have initialEntry := hyp.1.1
    have nextClock : decClock {s with clock := (extra + k) + 1} = {s with clock := extra + k} := by
      simp [decClock]
    have whole : badFunReturn result = false := by
      have h := InitSemantics.callNotBad start {middle with clock := extra + k}
      rw [targetRun] at h
      exact h
    refine ⟨extra, targetPost, ?_, ffi, ?_⟩
    · rw [evaluate_call]
      simp only [findCode, initialEntry, Nat.add_one_ne_zero, if_false]
      rw [nextClock, StackSemEvaluateClock.fixClockEvaluate, evaluate_seq,
        StackSemEvaluateClock.fixClockEvaluate, initClock]
      dsimp only
      simp only [targetRun, whole, Bool.false_eq_true, if_false]
    · have h := initEntrySteps gen maxHeap pointer start {s with clock := (extra + k) + 1}
        {middle with clock := extra + k} initialEntry (by simp) (by simpa [nextClock] using initClock)
      exact h.trans (Nat.add_le_add_left cost _)
end SteppedFlapjack.StackRemoveSteps
