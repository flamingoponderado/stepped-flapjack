import SteppedFlapjack.WordInstSteps.Loop
import SteppedFlapjack.WordToStackSteps.CallSequenceCost

/-! Instruction-selected Word loops composed with Word-to-Stack. -/
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open SteppedFlapjack.WordToStackSteps

/-- A non-error, non-timeout Word loop run yields an actual bounded Stack
execution after instruction selection and Word-to-Stack compilation. -/
theorem selectedLoop_stack_bounded {C F : Type}
    (ac : AsmConfigExact 64) (temp : Nat) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64)) (shape : SimpleProgram body)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × C) F)
    (result : Option (WordSemResult 64)) (locals : Spt (WordLocW 64))
    (target : StackSemStateFiniteExact 64 C F) (k f frame limit : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64)
    (run : evaluate (.loop names body exitNames) source = (result,sourcePost))
    (nonerror : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (vars : everyVarHOL (fun x => decide (x < temp)) (.loop names body exitNames) = true)
    (localRel : wordLocalsRel temp source.locals locals)
    (sourceBound : WordSteps.steps (.loop names body exitNames) source ≤ limit)
    (noInstallCode : WordProps.noInstallCode source.code)
    (code : ∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q)
    (stackPremises : stateRel ac k f frame {source with locals := locals} target lens 0 ∧
      postAllocConventionsHOL k (instSelect ac temp (.loop names body exitNames)) = true ∧
      compNative ac false (instSelect ac temp (.loop names body exitNames)) (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (instSelect ac temp (.loop names body exitNames)) < 2*frame+2*k) :
    ∃ localsPost targetPost targetResult,
      evaluate (instSelect ac temp (.loop names body exitNames)) {source with locals := locals} =
        (result,{sourcePost with locals := localsPost}) ∧
      StackSemEvaluate.evaluate (compiled,{target with clock := (1 + sizeOf (instSelect ac temp body)) * limit}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k f frame
        {source with locals := locals, clock := (1 + sizeOf (instSelect ac temp body)) * limit}
        {sourcePost with locals := localsPost, clock := (1 + sizeOf (instSelect ac temp body)) * limit - (source.clock-sourcePost.clock)}
        targetPost result targetResult lens ∧
      StackSteps.steps (compiled,{target with clock := (1 + sizeOf (instSelect ac temp body)) * limit}) ≤
        callSequenceCost ac ((1 + sizeOf (instSelect ac temp body)) * limit) target.code
          (instSelect ac temp (.loop names body exitNames)) (bs,n) (k,f,frame) := by
  obtain ⟨localsPost,selectedRun,_,selectedBound⟩ :=
    selectedLoop_correct_with_steps ac temp names exitNames body shape source sourcePost result locals
      run vars nonerror localRel
  have bound : WordSteps.steps (instSelect ac temp (.loop names body exitNames))
      {source with locals := locals} ≤ (1 + sizeOf (instSelect ac temp body)) * limit :=
    Nat.le_trans selectedBound (Nat.mul_le_mul_left _ sourceBound)
  have block : LoopBlock (instSelect ac temp (.loop names body exitNames)) := by
    simp only [instSelect]
    exact .loop _ _ (simple_selected_block shape ac temp)
  have noInstall : noInstallSubprogsHOL (instSelect ac temp (.loop names body exitNames)) = true := by
    simpa only [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using
      simple_selected_noInstall shape ac temp
  have flat : flatExpConventions (instSelect ac temp (.loop names body exitNames)) = true := by
    simpa only [instSelect,flatExpConventions] using simple_selected_flat shape ac temp
  obtain ⟨targetPost,targetResult,targetRun,targetRelation,targetBound⟩ :=
    callSequence_bounded ac _ (.block block) {source with locals := locals} {sourcePost with locals := localsPost}
      target result k f frame bs bsPost n nPost ((1 + sizeOf (instSelect ac temp body)) * limit)
      compiled lens noInstall noInstallCode code notTimeout bound
      ⟨selectedRun,nonerror,stackPremises.1,stackPremises.2.1,flat,stackPremises.2.2⟩
  exact ⟨localsPost,targetPost,targetResult,selectedRun,targetRun,targetRelation,targetBound⟩

end SteppedFlapjack.WordInstSteps
