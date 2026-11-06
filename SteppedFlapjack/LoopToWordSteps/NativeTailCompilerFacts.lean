import SteppedFlapjack.LoopToWordSteps.NativeTailRiscVReady
import SteppedFlapjack.WordAllocSteps.WholeTailCode

/-! Compiler-derived Word and Stack premises for a native Loop entry. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect Flapjack.WordAlloc
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Compiler.Backend.WordToWord Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordSimp
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackAllocSteps

/-- The whole compiler and a valid native Stack initialization derive the
Word code-table and frame premises for the actual Loop entry. Insufficient
stack space instead gives an actual bounded Stack resource outcome. -/
theorem nativeTail_compilerFacts_or_resource {F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat) (name : Nat)
    (shapes : TailProgramShapes programs)
    (member : (name,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : stack.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix stack.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) (limit : Nat) :
    let k := ac.regCount-(5+ac.avoidRegs.length)
    let compiledCode := sptFromAList (compile wc ac programs).2
    let originalCode := sptFromAList programs
    let q := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
      ((name,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs name)).2.2
    let replay := tailWordReplayLimit p ctxt labels compiledCode limit
    let stackReplay := tailStackReplayLimit ac 1 name wc.regAlg k (entryColour wc programs name) p ctxt labels compiledCode limit
    ∃ bs n bsPost nPost body frame frameSize,
      nativeEntryBitmap ac false k name (compile wc ac programs).2 (.list [4],1) = some (bs,n) ∧
      frame = max (maxVarHOL q / 2 + 1 - k) (1-k) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      compNative ac false q (bs,n) (k,frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup name stack.code = some (compileProgNative ac false q 1 k (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ stack.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (stack.bitmaps.drop (n-(appListAppend bs).length)) ∧
      let word := {callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
        (makeInit ac k stack compiledCode coracle) with code := originalCode}
      (WordProps.noInstallCode word.code ∧ codeRel word.code compiledCode ∧
        sptDomain word.code = sptDomain compiledCode ∧
        sptDomain word.locals = (fun key => key ∈ Flapjack.Compiler.Backend.WordAlloc.evenList 1) ∧
        wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals word.locals ∧
        sptLookup 0 word.locals = some (.loc 1 0) ∧
        (∀ loc, StackSem.getLabelsExact body loc → StackSem.locCheckExact stack.code loc) ∧
        maxVarHOL q < 2*frame+2*k ∧ frameSize-(1-k) ≤ stack.stackSpace ∧
        stateRel ac k frameSize frame {word with code := compiledCode,locals := word.locals,clock := replay}
          {stack with stackSpace := stack.stackSpace-(frameSize-(1-k)),clock := replay} [] 0) ∨
      ∃ post, StackSemEvaluate.evaluate (.call none (.inl name) none,{stack with clock := stackReplay+1}) =
          (some (.halt (.word 2)),post) ∧ post.ffi = stack.ffi ∧
        SteppedFlapjack.StackSteps.steps (.call none (.inl name) none,{stack with clock := stackReplay+1}) ≤ 3 := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let compiledCode := sptFromAList (compile wc ac programs).2
  let originalCode := sptFromAList programs
  let q := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
    ((name,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs name)).2.2
  let replay := tailWordReplayLimit p ctxt labels compiledCode limit
  let stackReplay := tailStackReplayLimit ac 1 name wc.regAlg k (entryColour wc programs name) p ctxt labels compiledCode limit
  obtain ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,native,found,lengthBound,bitmapBound,bitmapPrefix,frameResult⟩ :=
    wholeWordStack_tailEntryFrame_or_resource wc ac programs name (LoopToWord.compHOL ctxt p labels).1 member nodup
      stack coracle noRaise noStore codeEq bitmapsPrefix ok stackReplay
  refine ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,native,found,lengthBound,bitmapBound,bitmapPrefix,?_⟩
  rcases frameResult with ⟨fits,related,_⟩ | resource
  · left
    have kBound : 1 ≤ k := by have h := ok.1; dsimp [k]; omega
    have argSpace : 1-k = 0 := by omega
    have argSpace' : 1-(ac.regCount-(5+ac.avoidRegs.length)) = 0 := by simpa [k] using argSpace
    obtain ⟨noInstall,_,codeRel,codeDomain,_⟩ := wholeCompile_tail_codeRelations wc ac programs shapes
    have localFacts := initializedTail_simulation_state ac k frameSize frame stack compiledCode originalCode coracle
      replay (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) related
    obtain ⟨maxBound,labelCheck⟩ := nativeEntry_frame_and_labels ac k frame frameSize 1 name q stack
      bs bsPost n nPost body frameDef sizeDef native found
    refine ⟨?_,?_,?_,localFacts.1,localFacts.2.1,localFacts.2.2.1,labelCheck,maxBound,?_,?_⟩
    · simpa [originalCode] using noInstall
    · simpa [originalCode,compiledCode] using codeRel
    · simpa [originalCode,compiledCode] using codeDomain
    · simpa only [argSpace',Nat.sub_zero] using fits
    · simpa only [argSpace',Nat.sub_zero] using localFacts.2.2.2
  · exact Or.inr resource

end SteppedFlapjack.LoopToWordSteps
