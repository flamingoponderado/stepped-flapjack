import SteppedFlapjack.StackNamesSteps

/-! Compile-time checks of the `stack_names` step preservation. -/

namespace SteppedFlapjack.Test.StackNamesSteps

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackNames
open Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps SteppedFlapjack.StackNamesSteps
open SteppedFlapjack.StackNamesSteps.CompCorrect

variable {width : Nat} [NeZero width] {C F : Type}
  {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}

-- Renaming preserves the step count exactly.
example {p : HolProg width} {s : StackSemStateFiniteExact width C F}
    (hf : Function.Bijective (findNameSpt f)) (hpre : Pre c f s) :
    steps (progCompHOL f p, renameState c f s) = steps (p, s) :=
  steps_progCompHOL p s hf hpre

-- The conjunction with `comp_correct`.
example {p : HolProg width} {s : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {t : StackSemStateFiniteExact width C F}
    (h : evaluate (p, s) = (r, t) ∧ Function.Bijective (findNameSpt f) ∧
      ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧
      s.compile = (fun cfg => c cfg ∘ compileHOL f)) :
    evaluate (progCompHOL f p, renameState c f s) = (r, renameState c f t) ∧
      steps (progCompHOL f p, renameState c f s) = steps (p, s) :=
  compCorrectWithin p s r t h

-- The strengthened statement forgets to `comp_correct`.
example {p : HolProg width} {s : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {t : StackSemStateFiniteExact width C F}
    (h : evaluate (p, s) = (r, t) ∧ Function.Bijective (findNameSpt f) ∧
      ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧
      s.compile = (fun cfg => c cfg ∘ compileHOL f)) :
    evaluate (progCompHOL f p, renameState c f s) = (r, renameState c f t) :=
  compCorrect_of_within p s r t h

-- A returning `Call` without a return program is a single step.
example (dest : Sum Nat Nat) (h : HolProg width × Nat × Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps ((.call none dest (some h) : HolProg width), s) = 1 :=
  steps_call_none_some dest h s

-- `make_init` is the source state of the target state.
example {s : StackSemStateFiniteExact width C F} {code : List (Nat × HolProg width)}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    (hf : Function.Bijective (findNameSpt f))
    (hcode : s.code = sptFromAList (compileHOL f code))
    (hor : s.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle) :
    renameState s.compile f (makeInit f (sptFromAList code) oracle s) = s :=
  renameState_makeInit hf hcode hor

-- The shape of the bounded entry run: the target run takes the same number of
-- steps as the source run, with the same outcome and the renamed final state.
example {start k n : Nat} {s : StackSemStateFiniteExact width C F}
    {code : List (Nat × HolProg width)}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {res : Option (StackSemResult width)} {s' : StackSemStateFiniteExact width C F}
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : s.code = sptFromAList (compileHOL f code))
    (hor : s.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (ev : evaluate ((.call none (.inl start) none : HolProg width),
      { makeInit f (sptFromAList code) oracle s with clock := k }) = (res, s'))
    (hn : steps ((.call none (.inl start) none : HolProg width),
      { makeInit f (sptFromAList code) oracle s with clock := k }) ≤ n) :
    ∃ t' : StackSemStateFiniteExact width C F,
      evaluate ((.call none (.inl start) none : HolProg width), { s with clock := k }) = (res, t') ∧
      steps ((.call none (.inl start) none : HolProg width), { s with clock := k }) ≤ n ∧
      t' = renameState s.compile f s' :=
  stackNamesSemanticsWithin ha hs hk hf hcode hor ev hn

end SteppedFlapjack.Test.StackNamesSteps
