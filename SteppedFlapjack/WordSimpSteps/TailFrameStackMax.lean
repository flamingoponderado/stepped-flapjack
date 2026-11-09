import SteppedFlapjack.WordSimpSteps.StackMaximum
import SteppedFlapjack.WordSimpSteps.TailCallBound
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact
variable {width : Nat} [NeZero width] {C F : Type}

/-- A direct tail call uses at most one base word and its callee frame. -/
theorem directTail_frame_stackMax (loc size : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (1,callee))
    (frame : sptLookup loc s.stackSize = some size)
    (empty : s.stack = []) (maximum : s.stackMax = some 1) :
    (evaluate (.call none (some loc) [0] none) s).2.stackMax = some 1 ∨
      (evaluate (.call none (some loc) [0] none) s).2.stackMax = some (1+size) := by
  cases hvar : getVar 0 s with
  | none =>
    left
    rw [evaluate]
    simp [WordSemStateFiniteExact.getVars,hvar,maximum]
  | some value =>
    have args : WordSemStateFiniteExact.getVars [0] s = some [value] := by simp [WordSemStateFiniteExact.getVars,hvar]
    have found : wordSemFindCode (some loc) [value] s.code s.stackSize = some ([value],callee,some size) := by
      simp [wordSemFindCode,lookup,frame]
    rw [evaluate]
    simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,found,Option.some_ne_none, false_and,decide_false,Bool.false_eq_true,if_false]
    by_cases hz : s.clock = 0
    · left; simp [hz,flushState,maximum]
    · right
      simp only [hz]
      have h := loopSequence_stackMax shape (WordSemStateFiniteExact.callEnv [value] (some size) (decClock s))
      have init : (WordSemStateFiniteExact.callEnv [value] (some size) (decClock s)).stackMax = some (1+size) := by
        simp [WordSemStateFiniteExact.callEnv,decClock,maximum,empty,wordSemStackSize,wordSemOptionMax,wordSemOptionAdd]
      rw [init] at h
      rcases he : evaluate callee (WordSemStateFiniteExact.callEnv [value] (some size) (decClock s)) with ⟨result,post⟩
      rw [he] at h
      simp only [dite_false]
      split <;> exact h

/-- The same frame bound holds after the native entry move. -/
theorem moveTail_frame_stackMax (loc size : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (1,callee))
    (frame : sptLookup loc s.stackSize = some size)
    (empty : s.stack = []) (maximum : s.stackMax = some 1) :
    (evaluate (.seq (.move 1 [(0,0)]) (.call none (some loc) [0] none)) s).2.stackMax = some 1 ∨
      (evaluate (.seq (.move 1 [(0,0)]) (.call none (some loc) [0] none)) s).2.stackMax = some (1+size) := by
  cases hvar : getVar 0 s with
  | none =>
    left
    rw [evaluate,fix_clock_evaluate,evaluate]
    simp [WordSemStateFiniteExact.getVars,hvar,maximum]
  | some value =>
    have tail := directTail_frame_stackMax loc size callee shape
      (WordSemStateFiniteExact.setVars [0] [value] s)
      (by simpa [WordSemStateFiniteExact.setVars] using lookup)
      (by simpa [WordSemStateFiniteExact.setVars] using frame)
      (by simpa [WordSemStateFiniteExact.setVars] using empty)
      (by simpa [WordSemStateFiniteExact.setVars] using maximum)
    rw [evaluate,fix_clock_evaluate,evaluate]
    simpa [WordSemStateFiniteExact.getVars,hvar] using tail

end SteppedFlapjack.WordSimpSteps
