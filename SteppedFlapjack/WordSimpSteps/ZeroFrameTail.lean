import SteppedFlapjack.WordSimpSteps.StackMaximum
import SteppedFlapjack.WordSimpSteps.TailCallBound
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}
/-- A zero-frame tail call into a call-free loop body preserves the initial
stack maximum when the current stack is empty. -/
theorem directTail_zeroFrame_stackMax (loc : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (1,callee))
    (size : sptLookup loc s.stackSize = some 0)
    (empty : s.stack = []) (maximum : s.stackMax = some 1) :
    (evaluate (.call none (some loc) [0] none) s).2.stackMax = some 1 := by
  cases hvar : getVar 0 s with
  | none =>
    rw [evaluate]
    simp [WordSemStateFiniteExact.getVars,hvar,maximum]
  | some value =>
    have args : WordSemStateFiniteExact.getVars [0] s = some [value] := by simp [WordSemStateFiniteExact.getVars,hvar]
    have found : wordSemFindCode (some loc) [value] s.code s.stackSize = some ([value],callee,some 0) := by
      simp [wordSemFindCode,lookup,size]
    rw [evaluate]
    simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,found,Option.some_ne_none, false_and,decide_false,Bool.false_eq_true,if_false]
    by_cases hz : s.clock = 0
    · simp [hz,flushState,maximum]
    · simp only [hz]
      have h := loopSequence_stackMax shape (WordSemStateFiniteExact.callEnv [value] (some 0) (decClock s))
      have init : (WordSemStateFiniteExact.callEnv [value] (some 0) (decClock s)).stackMax = some 1 := by
        simp [WordSemStateFiniteExact.callEnv,decClock,maximum,empty,wordSemStackSize,wordSemOptionMax,wordSemOptionAdd]
      rw [init] at h
      rcases he : evaluate callee (WordSemStateFiniteExact.callEnv [value] (some 0) (decClock s)) with ⟨result,post⟩
      rw [he] at h
      simp only [dite_false]
      split <;> exact h
/-- A move followed by a zero-frame tail call preserves the one-word
maximum on an empty stack. -/
theorem moveTail_zeroFrame_stackMax (loc : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (1,callee))
    (size : sptLookup loc s.stackSize = some 0)
    (empty : s.stack = []) (maximum : s.stackMax = some 1) :
    (evaluate (.seq (.move 1 [(0,0)]) (.call none (some loc) [0] none)) s).2.stackMax = some 1 := by
  cases hvar : getVar 0 s with
  | none =>
    rw [evaluate,fix_clock_evaluate,evaluate]
    simp [WordSemStateFiniteExact.getVars,hvar,maximum]
  | some value =>
    have tail := directTail_zeroFrame_stackMax loc callee shape
      (WordSemStateFiniteExact.setVars [0] [value] s)
      (by simpa [WordSemStateFiniteExact.setVars] using lookup)
      (by simpa [WordSemStateFiniteExact.setVars] using size)
      (by simpa [WordSemStateFiniteExact.setVars] using empty)
      (by simpa [WordSemStateFiniteExact.setVars] using maximum)
    rw [evaluate,fix_clock_evaluate,evaluate]
    simpa [WordSemStateFiniteExact.getVars,hvar] using tail

end SteppedFlapjack.WordSimpSteps
