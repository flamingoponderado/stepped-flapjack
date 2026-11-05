import SteppedFlapjack.LoopToWordSteps.StackReady

/-! Explicit Loop-to-machine outcome and event correspondence. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Semantics.TargetProps
open SteppedFlapjack.StackToLabSteps

/-- Matching complete Loop and machine outcomes. -/
inductive LoopMachineOutcome : Option (LoopResultExact 64) → HolOutcome → Prop
  | returned (values) : LoopMachineOutcome (some (.result values)) .success
  | ffi (event) : LoopMachineOutcome (some (.finalFfi event)) (.ffiOutcome event)

/-- Matching completed Loop and Word results. -/
inductive LoopWordOutcome : Option (LoopResultExact 64) → Option (WordSemResult 64) → Prop
  | returned (values) : LoopWordOutcome (some (.result values)) (some (.result (.loc 1 0) values))
  | ffi (event) : LoopWordOutcome (some (.finalFfi event)) (some (.finalFfi event))

/-- Extract outcome correspondence from the original compiler relation. -/
theorem loopWordOutcome_of_resultCase {C F : Type} (ctxt : Spt Nat)
    (word wordPost : WordSemStateFiniteExact 64 C F) (loopPost : LoopSemStateFiniteExact 64 F)
    (loopResult : Option (LoopResultExact 64)) (wordResult : Option (WordSemResult 64))
    (complete : CompleteLoopResult loopResult)
    (relation : LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word loopResult loopPost wordResult wordPost) :
    LoopWordOutcome loopResult wordResult := by
  cases complete with
  | «return» values =>
    simp only [LoopToWord.CompileCorrect.resultCase] at relation
    rw [relation.2.1]
    exact .returned values
  | ffi event =>
    simp only [LoopToWord.CompileCorrect.resultCase] at relation
    rw [relation]
    exact .ffi event

/-- A complete Loop result and both original compiler relations imply either
matching outcomes and equal traces, or the explicitly detected stack-resource
case with a trace prefix and the source stack-limit overflow witness. -/
theorem loopMachine_correspondence {C F : Type} (ac : AsmConfigExact 64)
    (k f frame : Nat) (lens : List Nat)
    (word wordPost : WordSemStateFiniteExact 64 (Nat × C) F)
    (loopPost : LoopSemStateFiniteExact 64 F) (stackPost : StackSemStateFiniteExact 64 C F)
    (loopResult : Option (LoopResultExact 64)) (wordResult : Option (WordSemResult 64))
    (stackResult : Option (StackSemResult 64)) (outcome : HolOutcome) (machineFfi : HolFfiState F)
    (wordFfi : wordPost.ffi = loopPost.ffi)
    (loopRelation : LoopWordOutcome loopResult wordResult)
    (stackRelation : compCorrectResult ac k f frame word wordPost stackPost wordResult stackResult lens)
    (classification : stackEntryClass stackResult = .CompleteResult outcome)
    (events : machineFfi.ioEvents = stackPost.ffi.ioEvents) :
    (LoopMachineOutcome loopResult outcome ∧ machineFfi.ioEvents = loopPost.ffi.ioEvents) ∨
    (outcome = .resourceLimitHit ∧ machineFfi.ioEvents <+: loopPost.ffi.ioEvents ∧
      wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit) := by
  classical
  unfold compCorrectResult at stackRelation
  split at stackRelation
  · right
    obtain ⟨resultEq,eventPrefix,overflow⟩ := stackRelation
    rw [resultEq] at classification
    have outcomeEq : outcome = .resourceLimitHit := by simpa [stackEntryClass] using classification.symm
    exact ⟨outcomeEq,by simpa [events,wordFfi] using eventPrefix,overflow⟩
  · left
    rename_i notMismatch
    have resultEq : wordResult.map compileResult = stackResult := by simpa using notMismatch
    cases loopRelation with
    | returned values =>
      simp only [Option.map_some,compileResult] at resultEq
      simp only at stackRelation
      rw [← resultEq] at classification
      have outcomeEq : outcome = .success := by simpa [stackEntryClass] using classification.symm
      subst outcome
      have sameFfi : stackPost.ffi = wordPost.ffi := stackRelation.1.2.2.2.1
      exact ⟨.returned values, by simpa [events,wordFfi] using congrArg HolFfiState.ioEvents sameFfi⟩
    | ffi event =>
      simp only [Option.map_some,compileResult] at resultEq
      simp only at stackRelation
      rw [← resultEq] at classification
      have outcomeEq : outcome = .ffiOutcome event := by simpa [stackEntryClass] using classification.symm
      subst outcome
      have sameFfi : wordPost.ffi = stackPost.ffi := stackRelation.1
      exact ⟨.ffi event, by simpa [events,wordFfi] using congrArg HolFfiState.ioEvents sameFfi.symm⟩

end SteppedFlapjack.LoopToWordSteps
