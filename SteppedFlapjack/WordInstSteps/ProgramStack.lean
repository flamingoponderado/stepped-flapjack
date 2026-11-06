import SteppedFlapjack.WordInstSteps.Compositional
import SteppedFlapjack.WordToStackSteps.CallSequenceCost

/-! Compositional instruction selection followed by Word-to-Stack. -/
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open SteppedFlapjack.WordToStackSteps

/-- A compositional Word source run yields an actual bounded Stack execution after
instruction selection and Word-to-Stack compilation. -/
theorem boundedProgram_stack_bounded {C F : Type}
    (ac : AsmConfigExact 64) (temp : Nat) (p : WordLangProgHOL (BitVec 64))
    (factor : Nat) (shape : BoundedProgram ac temp p factor) (source sourcePost : WordSemStateFiniteExact 64 (Nat × C) F)
    (result : Option (WordSemResult 64)) (locals : Spt (WordLocW 64))
    (target : StackSemStateFiniteExact 64 C F) (k f frame limit : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64)
    (run : evaluate p source = (result,sourcePost)) (nonerror : result ≠ some .error)
    (notTimeout : result ≠ some .timeOut)
    (vars : everyVarHOL (fun x => decide (x < temp)) p = true)
    (localRel : wordLocalsRel temp source.locals locals)
    (sourceBound : WordSteps.steps p source ≤ limit)
    (noInstallCode : WordProps.noInstallCode source.code)
    (code : ∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q)
    (stackPremises : stateRel ac k f frame {source with locals := locals} target lens 0 ∧
      postAllocConventionsHOL k (instSelect ac temp p) = true ∧
      compNative ac false (instSelect ac temp p) (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (instSelect ac temp p) < 2*frame+2*k) :
    ∃ localsPost targetPost targetResult,
      evaluate (instSelect ac temp p) {source with locals := locals} =
        (result,{sourcePost with locals := localsPost}) ∧
      StackSemEvaluate.evaluate (compiled,{target with clock := factor * limit}) = (targetResult,targetPost) ∧
      compCorrectResult ac k f frame {source with locals := locals, clock := factor * limit}
        {sourcePost with locals := localsPost, clock := factor * limit - (source.clock-sourcePost.clock)} targetPost result targetResult lens ∧
      StackSteps.steps (compiled,{target with clock := factor * limit}) ≤
        callSequenceCost ac (factor * limit) target.code (instSelect ac temp p) (bs,n) (k,f,frame) := by
  obtain ⟨localsPost,selectedRun,_⟩ :=
    inst_select_thm ac temp p source result sourcePost locals ⟨run,vars,nonerror,localRel⟩
  have block := boundedProgram_block ac temp shape
  have selectedBound := boundedProgram_steps (C := Nat × C) (F := F) ac temp shape
    source sourcePost result locals run nonerror vars localRel
  have bound : WordSteps.steps (instSelect ac temp p) {source with locals := locals} ≤ factor * limit := by
    exact Nat.le_trans selectedBound (Nat.mul_le_mul_left _ sourceBound)
  have callShape : CallSequence (instSelect ac temp p) := .block block
  obtain ⟨targetPost,targetResult,targetRun,targetRelation,targetBound⟩ :=
    callSequence_bounded ac _ callShape {source with locals := locals} {sourcePost with locals := localsPost}
      target result k f frame bs bsPost n nPost (factor * limit) compiled lens
      (boundedProgram_conventions ac temp shape).2 noInstallCode code notTimeout bound
      ⟨selectedRun,nonerror,stackPremises.1,stackPremises.2.1,
        (boundedProgram_conventions ac temp shape).1,stackPremises.2.2⟩
  exact ⟨localsPost,targetPost,targetResult,selectedRun,targetRun,targetRelation,targetBound⟩

end SteppedFlapjack.WordInstSteps
