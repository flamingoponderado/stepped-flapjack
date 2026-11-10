import SteppedFlapjack.WordToStackSteps.TailEntryFrame
import SteppedFlapjack.WordToStackSteps.ResourceSafeResult
import SteppedFlapjack.WordToStackSteps.TailFrameBound
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.StackSteps
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.WordSimpSteps

namespace SteppedFlapjack.WordToStackSteps

/-- The optimized entry chosen by the whole Word compiler. -/
noncomputable def nativeTailEntryCode (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (name : Nat)
    (p : WordLangProgHOL (BitVec 64)) : WordLangProgHOL (BitVec 64) :=
  (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
    ((name,1,p),entryColour wc programs name)).2.2

/-- The deterministic bitmap cursor at the compiled entry. -/
noncomputable def nativeTailEntryBitmap (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (name : Nat) : AppList (BitVec 64) × Nat :=
  (nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length)) name (compile wc ac programs).2 (.list [4],1)).getD (.nil,0)

/-- The native-initialized Word entry state at a given clock. -/
noncomputable def nativeTailEntryWord {C F : Type} (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (name : Nat)
    (p : WordLangProgHOL (BitVec 64)) (t : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64))) (clock : Nat) :=
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let q := nativeTailEntryCode wc ac programs name p
  {(callEnv [(.loc 1 0 : WordLocW 64)] (some (nativeEntryFrameSize k q))
    (makeInit ac k t (sptFromAList (compile wc ac programs).2) coracle)) with clock := clock}

/-- Explicit code-derived bound for the native Stack entry call. -/
noncomputable def nativeTailEntryBound (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (name : Nat)
    (p : WordLangProgHOL (BitVec 64)) (limit : Nat) : Nat :=
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let q := nativeTailEntryCode wc ac programs name p
  let code := sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2
  3 + callSequenceCost ac 0 code q (nativeTailEntryBitmap wc ac programs name)
    (k,nativeEntryFrameSize k q,nativeEntryFrame k q) * (limit+1)

/-- An initialized Word entry with fitting reachable frames simulates through the native Stack entry with an explicit visit bound. -/
theorem nativeTailEntry_span {C F : Type} (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (name : Nat) (p : WordLangProgHOL (BitVec 64)) (member : (name,1,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (t : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix t.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) t coracle)
    (fits : nativeEntryFrameSize (ac.regCount-(5+ac.avoidRegs.length)) (nativeTailEntryCode wc ac programs name p) ≤ t.stackSpace)
    (clock limit : Nat) (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 (Nat × C) F)
    (shape : RegTailShape (nativeTailEntryCode wc ac programs name p))
    (noInstall : noInstallSubprogsHOL (nativeTailEntryCode wc ac programs name p) = true)
    (noInstallCode : WordProps.noInstallCode (nativeTailEntryWord wc ac programs name p t coracle clock).code)
    (localCode : RegTailLocalCode (nativeTailEntryCode wc ac programs name p) (nativeTailEntryWord wc ac programs name p t coracle clock).code)
    (conventions : postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) (nativeTailEntryCode wc ac programs name p) = true)
    (flat : flatExpConventions (nativeTailEntryCode wc ac programs name p) = true)
    (run : evaluate (nativeTailEntryCode wc ac programs name p) (nativeTailEntryWord wc ac programs name p t coracle clock) = (result,post))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (complete : CompleteWordResult result)
    (framesFit :
      1 + nativeEntryFrameSize (ac.regCount-(5+ac.avoidRegs.length)) (nativeTailEntryCode wc ac programs name p) ≤ t.stack.length ∧
      ∀ loc, RegTailCalls (nativeTailEntryCode wc ac programs name p) loc →
        ∀ arity callee, sptLookup loc (sptFromAList (compile wc ac programs).2) = some (arity,callee) →
          1 + (compileProgNative ac false callee arity (ac.regCount-(5+ac.avoidRegs.length)) (.nil,0)).2.1 ≤ t.stack.length)
    (wordBound : SteppedFlapjack.WordSteps.steps (nativeTailEntryCode wc ac programs name p) (nativeTailEntryWord wc ac programs name p t coracle clock) ≤ limit) :
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (.call none (.inl name) none,{t with clock := limit+1}) = (targetResult,targetPost) ∧
      result.map compileResult = targetResult ∧ post.ffi = targetPost.ffi ∧
      steps (.call none (.inl name) none,{t with clock := limit+1}) ≤ nativeTailEntryBound wc ac programs name p limit := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let q := nativeTailEntryCode wc ac programs name p
  let f := nativeEntryFrame k q
  let sz := nativeEntryFrameSize k q
  let word := nativeTailEntryWord wc ac programs name p t coracle clock
  let stack := {t with stackSpace := t.stackSpace-sz,clock := clock}
  obtain ⟨bs,n,bsPost,nPost,body,selected,compilation,found,len,gap,bitmapPrefix,related⟩ :=
    wholeWordStack_tailEntryFrame_safe wc ac programs name p member nodup t coracle noRaise noStore codeEq bitmapsPrefix ok fits
  have bitmap : nativeTailEntryBitmap wc ac programs name = (bs,n) := by
    unfold nativeTailEntryBitmap
    rw [selected]
    rfl
  have rel : stateRel ac k sz f word stack [] 0 := by
    exact stateRel_setClocks ac k sz f _ _ [] 0 clock related
  have argSpace : 1-k = 0 := by have h := ok.1; dsimp [k]; omega
  have frameDef : f = max (maxVarHOL q / 2 + 1-k) (1-k) := rfl
  have sizeDef : sz = if f = 0 then 0 else f+1 := rfl
  have foundBody : sptLookup name t.code = some (.seq (.stackAlloc sz) body) := by
    change sptLookup name t.code = some (compileProgNative ac false q 1 k (bs,n)).1 at found
    simp only [compileProgNative] at found
    change sptLookup name t.code = some (.seq (.stackAlloc (sz-(1-k))) (compNative ac false q (bs,n) (k,sz,f)).1) at found
    rw [argSpace,Nat.sub_zero] at found
    have bodyEq : (compNative ac false q (bs,n) (k,sz,f)).1 = body := congrArg Prod.fst compilation
    rw [bodyEq] at found
    exact found
  have startStack : wordSemStackSize word.stack = some 1 := by rfl
  have startMax : word.stackMax = some (1+sz) := by
    simp [word,nativeTailEntryWord,k,q,sz,WordSemStateFiniteExact.callEnv,makeInit,wordSemStackSize,wordSemOptionMax,wordSemOptionAdd]
  have startLimit : word.stackLimit = t.stack.length := by rfl
  have calleeFrames : ∀ loc, RegTailCalls q loc → ∃ arity callee size,
      sptLookup loc word.code = some (arity,callee) ∧ LoopBlock callee ∧
      sptLookup loc word.stackSize = some size ∧ 1+size ≤ word.stackLimit := by
    intro loc call
    obtain ⟨arity,callee,lookup,calleeShape⟩ := localCode loc call
    let size := (compileProgNative ac false callee arity k (.nil,0)).2.1
    have sizeLookup : sptLookup loc word.stackSize = some size := by
      change sptLookup loc (sptMapi _ (sptFromAList (compile wc ac programs).2)) = _
      rw [sptLookupMapi]
      change sptLookup loc (sptFromAList (compile wc ac programs).2) = _ at lookup
      rw [lookup]
      rfl
    refine ⟨arity,callee,size,lookup,calleeShape,sizeLookup,?_⟩
    change 1+size ≤ t.stack.length
    exact framesFit.2 loc call arity callee lookup
  obtain ⟨used,postMax,usedFit,_⟩ := regTail_stackMax_bound shape word (1+sz) word.stackLimit
    startStack startMax (by simpa [startLimit,k,q,sz] using framesFit.1) noInstallCode calleeFrames
  have limitEq := evaluate_stack_limit q word result post run
  have safe : post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
    rw [run] at postMax
    simp only at postMax
    rw [postMax,Option.getD_some,limitEq]
    exact usedFit
  have ⟨maxBound,labels⟩ := nativeEntry_frame_and_labels ac k f sz 1 name q t bs bsPost n nPost body frameDef sizeDef compilation found
  have labelsStack : ∀ loc, StackSem.getLabelsExact body loc → StackSem.locCheckExact stack.code loc := labels
  obtain ⟨targetPost,targetResult,bodyRun,matchResult,ffi,cost⟩ :=
    regTail_bounded_linear_safe ac q shape word post stack result k sz f bs bsPost n nPost limit body []
      noInstall noInstallCode localCode notTimeout wordBound
      ⟨run,notError,rel,conventions,flat,compilation,len,gap,bitmapPrefix,labelsStack,maxBound⟩ safe
  have completed : ∃ outcome, stackEntryClass targetResult = .CompleteResult outcome := by
    rw [← matchResult]
    cases complete <;> simp [compileResult,stackEntryClass]
  obtain ⟨outcome,classified⟩ := completed
  have wrapped := allocatedBody_entry t name limit sz body targetResult targetPost outcome
    (callSequenceCost ac 0 stack.code q (bs,n) (k,sz,f) * (limit+1)) foundBody ok.2.2.2.1 fits bodyRun classified cost
  refine ⟨targetPost,targetResult,wrapped.1,matchResult,ffi,?_⟩
  simpa [nativeTailEntryBound,k,q,sz,f,stack,bitmap,codeEq] using wrapped.2.2

end SteppedFlapjack.WordToStackSteps
