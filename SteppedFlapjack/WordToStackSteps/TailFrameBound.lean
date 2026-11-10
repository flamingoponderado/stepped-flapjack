import SteppedFlapjack.WordSimpSteps.StackMaximum
import SteppedFlapjack.WordToStackSteps.DirectTailLocal
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.CodeOnlyGrows
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
namespace SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width] {C F : Type}
set_option maxHeartbeats 1000000 in
/-- Branch instructions preserve the frame-size table. -/
theorem branch_stackSize_preserved {p : WordLangProgHOL (BitVec width)} (hp : Branch p) :
    ∀ s : WordSemStateFiniteExact width C F, (evaluate p s).2.stackSize = s.stackSize := by
  induction hp with
  | seq ha hb iha ihb =>
    intro s
    rw [evaluate, fix_clock_evaluate]
    rcases h : evaluate _ s with ⟨res,t⟩
    have first := iha s
    rw [h] at first
    cases res with
    | none => simp only; exact (ihb t).trans first
    | some r => exact first
  | ite cmp r ri ha hb iha ihb =>
    intro s
    rw [evaluate]
    cases getVar r s <;> cases getVarImm ri s <;> simp only
    split <;> first | rfl | exact iha s | exact ihb s
  | assign _ _ | inst _ | move _ _ | get _ _ | opCurrHeap _ _ _ | set _ _ | store _ _ | skip | tick | ret _ _ | «break» _ | «continue» _ =>
    intro s
    rw [evaluate]
    repeat (first | split)
    all_goals try rfl
    all_goals try (rename_i h; have hh := instConstFull _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.2)
    all_goals try (rename_i h; have hh := memStoreConst _ _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    all_goals split <;> rfl


open SteppedFlapjack.WordToStackSteps
set_option maxHeartbeats 1000000 in
/-- Call-free, no-install code preserves the maximum stack usage. -/
theorem loopBlock_stackMax {p : WordLangProgHOL (BitVec width)} (hp : LoopBlock p) :
    noInstallSubprogsHOL p = true → ∀ s : WordSemStateFiniteExact width C F, (evaluate p s).2.stackMax = s.stackMax := by
  induction hp with
  | seq ha hb iha ihb =>
    intro ni s
    simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at ni
    rw [evaluate, fix_clock_evaluate]
    rcases h : evaluate _ s with ⟨res,t⟩
    have first := iha ni.1 s
    rw [h] at first
    cases res with
    | none => simp only; exact (ihb ni.2 t).trans first
    | some r => exact first
  | ite cmp r ri ha hb iha ihb =>
    intro ni s
    simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at ni
    rw [evaluate]
    cases getVar r s <;> cases getVarImm ri s <;> simp only
    split <;> first | rfl | exact iha ni.1 s | exact ihb ni.2 s
  | loop names exits h ih =>
    intro ni
    exact loop_stackMax names exits (ih ni)
  | install _ _ _ _ _ => simp [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | inst _ | ret _ _ | move _ _ | opCurrHeap _ _ _ | ffi _ _ _ _ _ _ | set _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ | get _ _ | locValue _ _ | skip | tick | «break» _ | «continue» _ =>
    intro ni s
    rw [evaluate]
    repeat (first | split)
    all_goals try rfl
    all_goals try (rename_i h; have hh := instConstFull _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.1)
    all_goals try (split <;> rfl)
    all_goals repeat (first | split)
    all_goals rfl

set_option maxHeartbeats 1000000 in
/-- A tail call adds its callee frame to the existing stack usage. -/
theorem directTail_stackMax_bound (loc size m L arity stackWords : Nat) (args : List Nat)
    (callee : WordLangProgHOL (BitVec width))
    (shape : LoopBlock callee) (noInstall : noInstallSubprogsHOL callee = true)
    (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (arity,callee)) (frame : sptLookup loc s.stackSize = some size)
    (argsArity : args.length = arity)
    (stack : wordSemStackSize s.stack = some stackWords) (maximum : s.stackMax = some m)
    (mFits : m ≤ L) (frameFits : stackWords+size ≤ L) :
    ∃ m', (evaluate (.call none (some loc) args none) s).2.stackMax = some m' ∧ m' ≤ L ∧
      (evaluate (.call none (some loc) args none) s).1 ≠ none := by
  cases hv : WordSemStateFiniteExact.getVars args s with
  | none =>
    refine ⟨m,?_,mFits,?_⟩ <;> rw [evaluate] <;> simp [hv,maximum]
  | some values =>
    have len : values.length = arity := (WordSemStateFiniteExact.getVarsLengthLemma args s values hv).trans argsArity
    have found : wordSemFindCode (some loc) values s.code s.stackSize = some (values,callee,some size) := by
      simp [wordSemFindCode,lookup,frame,len]
    by_cases hz : s.clock = 0
    · refine ⟨m,?_,mFits,?_⟩ <;> rw [evaluate] <;> simp [hv,wordSemBadDestArgs,wordSemAddRetLoc,found,hz,flushState,maximum]
    · let env := WordSemStateFiniteExact.callEnv values (some size) (decClock s)
      have init : env.stackMax = some (max m (stackWords+size)) := by
        simp [env,WordSemStateFiniteExact.callEnv,decClock,maximum,stack,wordSemOptionMax,wordSemOptionAdd]
      have h := loopBlock_stackMax shape noInstall env
      rw [init] at h
      rcases he : evaluate callee env with ⟨result,post⟩
      rw [he] at h
      refine ⟨max m (stackWords+size),?_,Nat.max_le.mpr ⟨mFits,frameFits⟩,?_⟩ <;> rw [evaluate]
      · simp only [hv,wordSemBadDestArgs,wordSemAddRetLoc,found,hz,↓reduceDIte,Option.some_ne_none,false_and,decide_false,Bool.false_eq_true,if_false]
        rw [show evaluate callee (WordSemStateFiniteExact.callEnv values (some size) (decClock s)) = (result,post) from he]
        change (if wordSemBadFunReturn result then (some .error,post) else (result,post)).2.stackMax = _
        split <;> exact h
      · simp only [hv,wordSemBadDestArgs,wordSemAddRetLoc,found,hz,↓reduceDIte,Option.some_ne_none,false_and,decide_false,Bool.false_eq_true,if_false]
        rw [show evaluate callee (WordSemStateFiniteExact.callEnv values (some size) (decClock s)) = (result,post) from he]
        change (if wordSemBadFunReturn result then (some .error,post) else (result,post)).1 ≠ none
        cases result with
        | none => simp [wordSemBadFunReturn]
        | some r => split <;> simp

open SteppedFlapjack.WordAllocSteps
set_option maxHeartbeats 1000000 in
/-- Every reachable callee frame bounds the maximum usage of a tail entry. -/
theorem regTail_stackMax_bound {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
  ∀ (s : WordSemStateFiniteExact width C F) (m L : Nat),
    wordSemStackSize s.stack = some 1 → s.stackMax = some m → m ≤ L → WordProps.noInstallCode s.code →
    (∀ loc, RegTailCalls p loc → ∃ arity callee size, sptLookup loc s.code = some (arity,callee) ∧
      LoopBlock callee ∧ sptLookup loc s.stackSize = some size ∧ 1+size ≤ L) →
    ∃ m', (evaluate p s).2.stackMax = some m' ∧ m' ≤ L ∧
      ((evaluate p s).1 = none → (evaluate p s).2.stackSize = s.stackSize) := by
  induction shape with
  | branch h =>
    intro s m L stack maximum fits noCode code
    exact ⟨m,(branch_stackMax h s).trans maximum,fits,fun _ => branch_stackSize_preserved h s⟩
  | call loc reg =>
    intro s m L stack maximum fits noCode code
    obtain ⟨arity,callee,size,lookup,calleeShape,frame,frameFits⟩ := code loc (.call loc reg)
    by_cases arityOne : arity = 1
    · subst arity
      have noInstall := noCode loc 1 callee lookup
      obtain ⟨m',max',bound,notNone⟩ := directTail_stackMax_bound loc size m L 1 1 [reg] callee calleeShape noInstall s lookup frame rfl stack maximum fits frameFits
      exact ⟨m',max',bound,fun h => False.elim (notNone h)⟩
    · cases hvar : getVar reg s with
      | none =>
        refine ⟨m,?_,fits,?_⟩ <;> rw [evaluate] <;> simp [WordSemStateFiniteExact.getVars,hvar,maximum]
      | some value =>
        have found : wordSemFindCode (some loc) [value] s.code s.stackSize = none := by
          simp [wordSemFindCode,lookup,Ne.symm arityOne]
        refine ⟨m,?_,fits,?_⟩ <;> rw [evaluate] <;> simp [WordSemStateFiniteExact.getVars,hvar,wordSemBadDestArgs,wordSemAddRetLoc,found,maximum]

  | @seq a b ha hb iha ihb =>
    intro s m L stack maximum fits noCode code
    have codeA := fun loc h => code loc (.left h)
    have codeB := fun loc h => code loc (.right h)
    obtain ⟨ma,maxA,boundA,sizeA⟩ := iha s m L stack maximum fits noCode codeA
    rw [evaluate,fix_clock_evaluate]
    rcases run : evaluate a s with ⟨result,mid⟩
    rw [run] at maxA sizeA
    cases result with
    | some r => exact ⟨ma,maxA,boundA,by simp⟩
    | none =>
      have sizeEq : mid.stackSize = s.stackSize := sizeA rfl
      have stackEq := WordSemStackEq.evaluate_NONE_stack_size_const a s mid run
      have codeEq : mid.code = s.code := by
        have h := WordSemStateFiniteExact.code_evaluate a s (regTail_noInstall ha) noCode
        rw [run] at h
        exact h
      have bCode : ∀ loc, RegTailCalls b loc → ∃ arity callee size, sptLookup loc mid.code = some (arity,callee) ∧
          LoopBlock callee ∧ sptLookup loc mid.stackSize = some size ∧ 1+size ≤ L := by
        intro loc call
        simpa only [codeEq,sizeEq] using codeB loc call
      obtain ⟨mb,maxB,boundB,sizeB⟩ := ihb mid ma L (stackEq.trans stack) maxA boundA
        (by simpa only [codeEq] using noCode) bCode
      refine ⟨mb,maxB,boundB,?_⟩
      intro hn
      exact (sizeB hn).trans sizeEq
end SteppedFlapjack.WordSimpSteps
