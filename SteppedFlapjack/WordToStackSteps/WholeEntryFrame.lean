import SteppedFlapjack.WordToStackSteps.InitialFrame
import SteppedFlapjack.WordToStackSteps.EntryComposition

/-! The actual compiled initial entry either obtains its frame or hits the
native Stack resource limit. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs.InitializationStateRel
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackAllocSteps

/-- The native compiler-selected one-argument entry either starts in the
proved frame relation or takes the actual bounded Stack resource-limit path. -/
theorem wholeWordStack_entryFrame_or_resource {C F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (name : Nat) (p : WordLangProgHOL (BitVec 64)) (member : (name,1,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup) (shape : LoopSequence p)
    (t : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix t.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) t coracle)
    (limit : Nat) :
    ∃ col q bs n bsPost nPost body frame frameSize,
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,1,p),col)).2.2 ∧
      LoopBlock q ∧ noInstallSubprogsHOL q = true ∧ flatExpConventions q = true ∧
      postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) q = true ∧
      frame = max (maxVarHOL q / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (1-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      compNative ac false q (bs,n) (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup name t.code = some (compileProgNative ac false q 1 (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ t.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (t.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) t (sptFromAList (compile wc ac programs).2) coracle))
        {t with stackSpace := t.stackSpace-frameSize} [] 0 ∧
       stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        {(callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) t (sptFromAList (compile wc ac programs).2) coracle)) with clock := limit}
        {t with stackSpace := t.stackSpace-frameSize,clock := limit} [] 0 ∨
       ∃ post, StackSemEvaluate.evaluate (.call none (.inl name) none,{t with clock := limit+1}) =
            (some (.halt (.word 2)),post) ∧ post.ffi = t.ffi ∧
          StackSteps.steps (.call none (.inl name) none,{t with clock := limit+1}) ≤ 3) := by
  obtain ⟨_,col,q,bs,n,bsPost,nPost,body,frame,frameSize,qDef,block,noInstall,flat,postAlloc,
    frameDef,sizeDef,compilation,found,lengthBound,gapBound,bitmapPrefix⟩ :=
    wholeWordStack_initialized_entry wc ac programs name 1 p member nodup shape t coracle noRaise noStore codeEq bitmapsPrefix ok
  have regBound : 1 ≤ ac.regCount-(5+ac.avoidRegs.length) := by have h := ok.1; omega
  have argSpace : 1-(ac.regCount-(5+ac.avoidRegs.length)) = 0 := by omega
  have foundBody : sptLookup name t.code = some (.seq (.stackAlloc frameSize) body) := by
    simp only [compileProgNative, ← frameDef, ← sizeDef, compilation] at found
    simpa only [argSpace,Nat.sub_zero] using found
  refine ⟨col,q,bs,n,bsPost,nPost,body,frame,frameSize,qDef,block,noInstall,flat,postAlloc,
    frameDef,sizeDef,compilation,found,lengthBound,gapBound,bitmapPrefix,?_⟩
  by_cases fits : frameSize ≤ t.stackSpace
  · left
    have frameShape : if frame = 0 then frameSize = 0 else frameSize = frame+1 := by
      split <;> simp_all
    have related := wholeWordStack_initialFrame wc ac programs t coracle noRaise noStore codeEq bitmapsPrefix ok
      frameSize frame frameShape fits
    exact ⟨related,stateRel_setClocks ac _ frameSize frame _ _ [] 0 limit related⟩
  · right
    obtain ⟨post,run,_,ffi,bound⟩ := allocationFailure_entry t name limit frameSize body foundBody ok.2.2.2.1 (by omega)
    exact ⟨post,run,ffi,bound⟩

end SteppedFlapjack.WordToStackSteps
