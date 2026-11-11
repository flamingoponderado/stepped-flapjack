import SteppedFlapjack.WordToStackSteps.WholeCallBudget
import SteppedFlapjack.WordToStackSteps.ResourceSafeResult
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

private theorem startCall_compile {width : Nat} [NeZero width] (ac : AsmConfigExact width) (k loc : Nat) :
  compNative ac false (.call none (some loc) [0] none) ((.list [] : AppList (BitVec width)),0) (k,0,0) =
    (.seq .skip (.call none (.inl loc) none),(.list [],0)) := by
  simp [compNative,callDestNative,seqStackFreeNative,Compiler.Backend.WordToStack.stackFree,
    Compiler.Backend.WordToStack.stackArgCount]

/-- The Word start call induces the actual Stack entry run at an explicit clock. -/
theorem wordStack_startCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k loc : Nat)
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (related : stateRel ac k 0 0 source target [] 0)
    (safe : safeWordCode source) (noAllocCode : WordProps.noAllocCode source.code)
    (empty : StackSteps.emptyCodeOracle target)
    (run : WordSemStateFiniteExact.evaluate (.call none (some loc) [0] none) source = (result,post))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut) :
    let allowance := callTableBudget (.call none (some loc) [0] none) source
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (.call none (.inl loc) none,{target with clock := target.clock + allowance}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k 0 0 source post {targetPost with clock := post.clock} result targetResult [] ∧
      StackSteps.steps (.call none (.inl loc) none,{target with clock := target.clock + allowance}) ≤
        1 + max 1 (StackSteps.stackCodeWeight target.code) * (target.clock + allowance) := by
  dsimp only
  have large : 4 < k := by
    unfold stateRel at related
    tauto
  have startNoMt : noMtSubprogsHOL ((.call none (some loc) [0] none) : WordLangProgHOL (BitVec width)) = true := by
    simp [noMtSubprogsHOL,notCreatedSubprogsWithMemOp]
  have startNoAlloc : noAllocSubprogsHOL ((.call none (some loc) [0] none) : WordLangProgHOL (BitVec width)) = true := by
    simp [noAllocSubprogsHOL,notCreatedSubprogsWithMemOp]
  have startNoInstall : noInstallSubprogsHOL ((.call none (some loc) [0] none) : WordLangProgHOL (BitVec width)) = true := by
    simp [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  have startFacts : WordSemStateFiniteExact.evaluate (.call none (some loc) [0] none) source = (result, post) ∧
      result ≠ some .error ∧ result ≠ some .timeOut ∧ stateRel ac k 0 0 source target [] 0 ∧
      postAllocConventionsHOL k ((.call none (some loc) [0] none) : WordLangProgHOL (BitVec width)) = true ∧
      flatExpConventions ((.call none (some loc) [0] none) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.call none (some loc) [0] none) ((.list [] : AppList (BitVec width)),0) (k,0,0) =
        (.seq .skip (.call none (.inl loc) none),(.list [],0)) ∧
      (appListAppend (.list [] : AppList (BitVec width))).length ≤ 0 ∧
      0-(appListAppend (.list [] : AppList (BitVec width))).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend (.list [] : AppList (BitVec width))) (target.bitmaps.drop (0-(appListAppend (.list [] : AppList (BitVec width))).length)) ∧
      (∀ label, StackSem.getLabelsExact (.seq .skip (.call none (.inl loc) none) : HolProg width) label → StackSem.locCheckExact target.code label) ∧
      maxVarHOL ((.call none (some loc) [0] none) : WordLangProgHOL (BitVec width)) < 2*0+2*k := by
    refine ⟨run,notError,notTimeout,related,?_,?_,startCall_compile ac k loc,?_,?_,?_,?_,?_⟩
    · simp [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,callArgConventionHOL,isPhyVar]
    · rfl
    · simp [appListAppend,appendAux]
    · simp
    · simp [appListAppend,appendAux]
    · intro label member; simp [StackSem.getLabelsExact] at member
    · simp [maxVarHOL,maxList]; omega
  obtain ⟨targetPost,out,compiledRun,relation,_⟩ := callBudgetBlock_stackVisits ac
    (.call none (some loc) [0] none) source post target result k 0 0 (.list []) (.list []) 0 0
    (.seq .skip (.call none (.inl loc) none)) [] startNoMt startNoAlloc startNoInstall safe noAllocCode empty startFacts
  have actualRun : StackSemEvaluate.evaluate (.call none (.inl loc) none,
      {target with clock := target.clock + callTableBudget (.call none (some loc) [0] none) source}) = (out,targetPost) := by
    simpa [CallReturnEval.seq_skip_left] using compiledRun
  refine ⟨targetPost,out,actualRun,relation,?_⟩
  have bound := StackSteps.stackTable_clock_bound (.call none (.inl loc) none)
    {target with clock := target.clock + callTableBudget (.call none (some loc) [0] none) source} empty
  simpa [StackSteps.stackControlWeight] using bound
/-- With a satisfied source stack limit, the actual Stack entry run has the
same result and FFI state as the Word start call. -/
theorem wordStack_startCall_exact {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k loc : Nat)
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (related : stateRel ac k 0 0 source target [] 0)
    (safe : safeWordCode source) (noAllocCode : WordProps.noAllocCode source.code)
    (empty : StackSteps.emptyCodeOracle target)
    (run : WordSemStateFiniteExact.evaluate (.call none (some loc) [0] none) source = (result,post))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (stackBound : post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit) :
    let allowance := callTableBudget (.call none (some loc) [0] none) source
    ∃ targetPost,
      StackSemEvaluate.evaluate (.call none (.inl loc) none,{target with clock := target.clock + allowance}) =
        (result.map compileResult,targetPost) ∧ targetPost.ffi = post.ffi ∧
      StackSteps.steps (.call none (.inl loc) none,{target with clock := target.clock + allowance}) ≤
        1 + max 1 (StackSteps.stackCodeWeight target.code) * (target.clock + allowance) := by
  dsimp only
  obtain ⟨targetPost,out,stackRun,relation,visits⟩ :=
    wordStack_startCall ac k loc source post target result related safe noAllocCode empty run notError notTimeout
  have resultEq := compCorrectResult_of_stack_safe ac k 0 0 source post
    {targetPost with clock := post.clock} result out [] relation stackBound
  have ffiEq := compCorrectResult_ffi_of_match ac k 0 0 source post
    {targetPost with clock := post.clock} result out [] relation resultEq
  subst out
  exact ⟨targetPost,stackRun,ffiEq.symm,visits⟩

end SteppedFlapjack.WordToStackSteps
