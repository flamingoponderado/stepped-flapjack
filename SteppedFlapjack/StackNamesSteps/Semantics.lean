import SteppedFlapjack.StackNamesSteps.StepsPreservation
import Flapjack.Compiler.Backend.StackNames.Proofs.MakeInit

/-! Run-level step preservation for `stack_names` (stepped-flapjack#2, phase C2).

`make_init` builds the source state (uncompiled code, source register names)
whose `rename_state` is the target state `s`; this is the `compile_semantics_alt`
step of `make_init_semantics`. `renameState_makeInit` states that fact on its
own, and `stackNamesSemanticsWithin` composes it with `compCorrectWithin`: a
StackSem entry run of the source state that completes within `n` steps is
matched by the target run from `s` within the same `n` steps, with the same
outcome and with the final state renamed. The bound is exact; `stack_names`
adds nothing.

`Flapjack/Compiler/Backend/StackNames/Proofs/MakeInit.lean` is imported for the
definition `makeInit` and its finite-map lemma `mapKeys_mapKeys_linv`; the
run-level statement is proved here, not derived from `make_init_semantics`.

This is stepped-flapjack infrastructure with no HOL counterpart.
-/

namespace SteppedFlapjack.StackNamesSteps

open Flapjack Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.StackSemMeasure Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps
open SteppedFlapjack.StackNamesSteps.CompCorrect

variable {width : Nat} [NeZero width] {C F : Type}

/-- `make_init` is the source state whose `rename_state` is the target state
`t` (the `compile_semantics_alt` step of `make_init_semantics`). -/
theorem renameState_makeInit {s : StackSemStateFiniteExact width C F} {f : Spt Nat}
    {code : List (Nat × HolProg width)}
    {oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    (hf : Function.Bijective (findNameSpt f))
    (hcode : s.code = sptFromAList (compileHOL f code))
    (hor : s.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle) :
    renameState s.compile f (makeInit f (sptFromAList code) oracle s) = s := by
  have hinv : ∀ y, findNameSpt f (holLinv (findNameSpt f) (fun _ => True) y) = y :=
    apply_holLinv_of_surjective hf.2
  have hc : sptFromAList (compileHOL f (sptToAList (sptFromAList code))) = s.code := by
    rw [hcode]
    refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
    rw [sptLookup_sptFromAList, sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
      sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, sptLookup_sptFromAList,
      sptAListLookup_compileHOL]
  classical
  have hsave : (fun y => decide (∃ x, decide (∃ z, s.ffiSaveRegs z = true ∧
      x = holLinv (findNameSpt f) (fun _ => True) z) = true ∧ y = findNameSpt f x)) =
      s.ffiSaveRegs := by
    funext y
    by_cases hy : s.ffiSaveRegs y = true
    · rw [hy, decide_eq_true_iff]
      exact ⟨holLinv (findNameSpt f) (fun _ => True) y,
        decide_eq_true_iff.mpr ⟨y, hy, rfl⟩, (hinv y).symm⟩
    · rw [Bool.not_eq_true] at hy
      rw [hy, decide_eq_false_iff_not]
      rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := decide_eq_true_iff.mp hx
      rw [hinv z, hz] at hy
      exact Bool.noConfusion hy
  simp only [renameState, makeInit, MakeInit.mapKeys_mapKeys_linv hf, hc, ← hor]
  refine Eq.trans ?_ (show { s with ffiSaveRegs := s.ffiSaveRegs } = s from rfl)
  congr 1

/-- Bounded `stack_names` entry run: a source entry run from the `make_init`
state that completes with `res` within `n` steps is matched by the target run
from `s` within the same `n` steps, with the same outcome and the renamed final
state. -/
theorem stackNamesSemanticsWithin {start k n : Nat}
    {s : StackSemStateFiniteExact width C F} {f : Spt Nat}
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
      t' = renameState s.compile f s' := by
  have hrename := renameState_makeInit (C := C) (F := F) hf hcode hor
  have hstate : renameState s.compile f
      { makeInit f (sptFromAList code) oracle s with clock := k } = { s with clock := k } := by
    rw [renameState_withClock, hrename]
  have hpre : Pre s.compile f
      { makeInit f (sptFromAList code) oracle s with clock := k } := by
    refine ⟨?_, ?_, ?_, rfl⟩
    · simpa [makeInit] using ha
    · simpa [makeInit] using hs
    · simpa [makeInit] using hk
  obtain ⟨heval, hsteps⟩ :=
    compCorrectWithin (.call none (.inl start) none) _ res s' ⟨ev, hf, hpre⟩
  refine ⟨renameState s.compile f s', ?_, ?_, rfl⟩
  · rw [hstate] at heval
    exact heval
  · rw [hstate] at hsteps
    have hsame : steps ((.call none (.inl start) none : HolProg width), { s with clock := k }) =
        steps ((.call none (.inl start) none : HolProg width),
          { makeInit f (sptFromAList code) oracle s with clock := k }) := hsteps
    rw [hsame]
    exact hn

end SteppedFlapjack.StackNamesSteps
