import SteppedFlapjack.WordToStackSteps.InitialFrame
import SteppedFlapjack.WordToStackSteps.EntryComposition
import SteppedFlapjack.WordToStackSteps.WholeTailInitialization
import SteppedFlapjack.WordToStackSteps.FixedEntryFrame
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.Support

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

/-- The compiler-selected one-argument tail entry either starts in the
proved frame relation or takes the actual bounded Stack resource-limit path. -/
theorem wholeWordStack_tailEntryFrame_or_resource {C F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (name : Nat) (p : WordLangProgHOL (BitVec 64)) (member : (name,1,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (t : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix t.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) t coracle)
    (limit : Nat) :
    let q := (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,1,p),SteppedFlapjack.WordAllocSteps.entryColour wc programs name)).2.2
    ∃ bs n bsPost nPost body frame frameSize,
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
  obtain ⟨_,bs,n,bsPost,nPost,body,frame,frameSize,
    frameDef,sizeDef,compilation,found,lengthBound,gapBound,bitmapPrefix⟩ :=
    wholeWordStack_tail_initialized_inputs wc ac programs name 1 p member nodup t coracle noRaise noStore codeEq bitmapsPrefix ok
  have regBound : 1 ≤ ac.regCount-(5+ac.avoidRegs.length) := by have h := ok.1; omega
  have argSpace : 1-(ac.regCount-(5+ac.avoidRegs.length)) = 0 := by omega
  have foundBody : sptLookup name t.code = some (.seq (.stackAlloc frameSize) body) := by
    simp only [compileProgNative, ← frameDef, ← sizeDef, compilation] at found
    simpa only [argSpace,Nat.sub_zero] using found
  refine ⟨bs,n,bsPost,nPost,body,frame,frameSize,
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


/-- The initialized frame gives the exact local-domain and state premises for
simulating an original Word entry against the compiled code table. Replacing
the code table does not alter entry locals or the frame relation once the
compiled table is restored for the Stack simulation. -/
theorem initializedTail_simulation_state {C F : Type}
    (ac : AsmConfigExact 64) (k frameSize frame : Nat)
    (stack : StackSemStateFiniteExact 64 C F)
    (compiledCode originalCode : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (clock temp : Nat)
    (related : stateRel ac k frameSize frame
      (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
        (makeInit ac k stack compiledCode coracle))
      {stack with stackSpace := stack.stackSpace-frameSize} [] 0) :
    let word := {callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
      (makeInit ac k stack compiledCode coracle) with code := originalCode}
    let entry := {stack with clock := clock}
    sptDomain word.locals = (fun key => key ∈ Flapjack.Compiler.Backend.WordAlloc.evenList 1) ∧
    wordLocalsRel temp word.locals word.locals ∧
    sptLookup 0 word.locals = some (.loc 1 0) ∧
    stateRel ac k frameSize frame {word with code := compiledCode,locals := word.locals,clock := clock}
      {entry with stackSpace := entry.stackSpace-frameSize} [] 0 := by
  have localFacts := nativeEntry_locals (makeInit ac k stack compiledCode coracle) frameSize temp
  have shifted := stateRel_setClocks ac k frameSize frame _ _ [] 0 clock related
  exact ⟨localFacts.1,localFacts.2.1,localFacts.2.2,by simpa [WordSemStateFiniteExact.callEnv,makeInit] using shifted⟩


/-- For the compiler-generated zero-argument context, the native Word entry
locals represent the empty Loop locals and every used Loop variable has a
context entry. -/
theorem nativeTailEntry_loopLocals {C F : Type} (p : HolLoopProg 64)
    (source : WordSemStateFiniteExact 64 C F) (frameSize : Nat) :
    let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln
    let word := callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) source
    LoopToWord.localsRelHOL ctxt .ln word.locals ∧
      ∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt := by
  have h := LoopToWord.CompileCorrect.compFunc_ctxt [] p [] (.loc 1 0 : WordLocW 64) (by simp) (by simp)
  simpa [WordSemStateFiniteExact.callEnv,sptFromAList] using h

end SteppedFlapjack.WordToStackSteps
