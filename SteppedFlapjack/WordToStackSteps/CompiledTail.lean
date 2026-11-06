import SteppedFlapjack.WordAllocSteps.CompiledCodeTail

/-! Actual compiled-table Word entries through Word-to-Stack. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc Flapjack.WordProps
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

/-- A source-bounded direct entry executes through the actual complete Word
compiler and native Word-to-Stack compiler on the related compiled table.
The callee shape required by Stack is derived from that table's code relation. -/
theorem compiledTail_stack_bound {C F : Type}
    (ac : AsmConfigExact width) (flag : Bool) (count fc alg k : Nat) (col : Option (Spt Nat))
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width (Nat × C) F) (res : Option (WordSemResult width))
    (targetCode : Spt (Nat × WordLangProgHOL (BitVec width))) (K limit : Nat) (locals : Spt (WordLocW width))
    (code : TailEntryCodeBound p s.code K) (noInstall : noInstallCode s.code)
    (rel : codeRel s.code targetCode) (domainCode : sptDomain s.code = sptDomain targetCode)
    (gc : gcFunConstOk s.gcFun) (run : evaluate p s = (res,post))
    (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : WordSteps.steps p s ≤ limit)
    (localsRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domainLocals : sptDomain locals = (fun key => key ∈ evenList count))
    (stack : StackSemStateFiniteExact width C F) (frameSize frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (stackRel : stateRel ac k frameSize frame
      {s with code := targetCode,locals := locals,clock := sizeOf p * (wordCodeSize targetCode+1) * (limit+1)} stack lens 0)
    (native : compNative ac false (fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2
      (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ stack.bitmaps.length)
    (bitmapPrefix : List.IsPrefix (appListAppend bsPost) (stack.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact stack.code loc)
    (maxBound : maxVarHOL (fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2 < 2*frame+2*k) :
    let out := (fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2
    let wordLimit := sizeOf p * (wordCodeSize targetCode+1) * (limit+1)
    let stackLimit := sizeOf out * (wordCodeSize targetCode+1) * (wordLimit+1)
    ∃ perm selectedLocals wordPost stackPost stackResult,
      wordStateEqRel {post with code := targetCode,permute := perm,locals := selectedLocals,clock := wordLimit-(limit-(limit-(s.clock-post.clock)))} wordPost ∧
      StackSemEvaluate.evaluate (compiled,{stack with clock := stackLimit}) = (stackResult,stackPost) ∧
      compCorrectResult ac k frameSize frame {s with code := targetCode,locals := locals,clock := stackLimit}
        {wordPost with clock := stackLimit-(wordLimit-wordPost.clock)} stackPost res stackResult lens ∧
      StackSteps.steps (compiled,{stack with clock := stackLimit}) ≤
        callSequenceCost ac stackLimit stack.code out (bs,n) (k,frameSize,frame) := by
  let wordLimit := sizeOf p * (wordCodeSize targetCode+1) * (limit+1)
  let out := (fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2
  let stackLimit := sizeOf out * (wordCodeSize targetCode+1) * (wordLimit+1)
  obtain ⟨outShape,localCode,outNoInstall,outFlat,outConvention,perm,selectedLocals,wordPost,wordRun,wordRel,wordBound⟩ :=
    fullCompileSingle_compiledCode_tailEntry_correct ac flag count fc alg k col shape s post res targetCode K limit locals
      code noInstall rel domainCode gc run nonerror notTimeout sourceBound localsRel domainLocals
  have compiledNoInstall := noInstallCode_of_codeRel s.code targetCode rel domainCode noInstall
  obtain ⟨stackPost,stackResult,stackRun,stackResultRel,stackBound⟩ :=
    regTail_bounded_local ac out outShape {s with code := targetCode,locals := locals,clock := wordLimit}
      wordPost stack res k frameSize frame bs bsPost n nPost stackLimit compiled lens
      outNoInstall compiledNoInstall localCode notTimeout wordBound
      ⟨wordRun,nonerror,stackRel,outConvention,outFlat,native,lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  exact ⟨perm,selectedLocals,wordPost,stackPost,stackResult,wordRel,stackRun,stackResultRel,stackBound⟩

end SteppedFlapjack.WordToStackSteps
