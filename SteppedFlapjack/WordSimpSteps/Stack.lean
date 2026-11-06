import SteppedFlapjack.WordSimpSteps.Selection
import SteppedFlapjack.WordInstSteps.ProgramStack

/-! WordSimp and instruction selection composed with Word-to-Stack. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.WordInstSteps
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open SteppedFlapjack.WordToStackSteps

/-- A supported Word loop runs through actual WordSimp, instruction selection,
and Word-to-Stack with a bound derived from the original Word visits. -/
theorem simp_select_loop_stack_bounded {C F : Type}
    (ac : AsmConfigExact 64) (temp : Nat) (names exits : Spt Unit)
    (body : WordLangProgHOL (BitVec 64)) (shape : Branch body)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × C) F)
    (result : Option (WordSemResult 64)) (locals : Spt (WordLocW 64))
    (target : StackSemStateFiniteExact 64 C F) (k f frame limit : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64)
    (run : evaluate (.loop names body exits) source = (result,sourcePost))
    (nonerror : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (gc : gcFunConstOk source.gcFun)
    (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp (.loop names body exits)) = true)
    (localRel : wordLocalsRel temp source.locals locals)
    (sourceBound : steps (.loop names body exits) source ≤ limit)
    (noInstallCode : WordProps.noInstallCode source.code)
    (code : ∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q)
    (stackPremises : stateRel ac k f frame {source with locals := locals} target lens 0 ∧
      postAllocConventionsHOL k (instSelect ac temp (compileExp (.loop names body exits))) = true ∧
      compNative ac false (instSelect ac temp (compileExp (.loop names body exits))) (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (instSelect ac temp (compileExp (.loop names body exits))) < 2*frame+2*k) :
    ∃ localsPost targetPost targetResult,
      evaluate (instSelect ac temp (compileExp (.loop names body exits))) {source with locals := locals} =
        (result,{sourcePost with locals := localsPost}) ∧
      StackSemEvaluate.evaluate (compiled,{target with clock := programFactor ac temp (compileExp (.loop names body exits)) * ((1 + sizeOf (compileExp body)) * limit)}) = (targetResult,targetPost) ∧
      compCorrectResult ac k f frame {source with locals := locals, clock := programFactor ac temp (compileExp (.loop names body exits)) * ((1 + sizeOf (compileExp body)) * limit)}
        {sourcePost with locals := localsPost, clock := programFactor ac temp (compileExp (.loop names body exits)) * ((1 + sizeOf (compileExp body)) * limit) - (source.clock-sourcePost.clock)}
        targetPost result targetResult lens ∧
      StackSteps.steps (compiled,{target with clock := programFactor ac temp (compileExp (.loop names body exits)) * ((1 + sizeOf (compileExp body)) * limit)}) ≤
        callSequenceCost ac (programFactor ac temp (compileExp (.loop names body exits)) * ((1 + sizeOf (compileExp body)) * limit))
          target.code (instSelect ac temp (compileExp (.loop names body exits))) (bs,n) (k,f,frame) := by
  have simpCorrect := compileExp_loop_branch_correct names exits shape source gc
  have simpRun : evaluate (compileExp (.loop names body exits)) source = (result,sourcePost) := simpCorrect.1.trans run
  have program : Program (compileExp (.loop names body exits)) := by
    rw [compileExp_loop]
    exact .loop names exits (branch_program (compileExp_branch shape))
  have simpBound : steps (compileExp (.loop names body exits)) source ≤ (1 + sizeOf (compileExp body)) * limit :=
    Nat.le_trans simpCorrect.2 (Nat.mul_le_mul_left _ sourceBound)
  exact boundedProgram_stack_bounded ac temp _ _ (program_factor ac temp program) source sourcePost result locals
    target k f frame _ lens bs bsPost n nPost compiled simpRun nonerror notTimeout vars localRel simpBound
    noInstallCode code stackPremises

end SteppedFlapjack.WordSimpSteps
