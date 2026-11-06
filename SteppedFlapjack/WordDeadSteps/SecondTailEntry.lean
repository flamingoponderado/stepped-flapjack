import SteppedFlapjack.WordDeadSteps.Second
import SteppedFlapjack.WordUnreachSteps.TailEntry

/-! Tail-entry composition through the second dead-code pass. -/
namespace SteppedFlapjack.WordDeadSteps
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordCseSteps
open SteppedFlapjack.WordCopySteps SteppedFlapjack.WordTwoRegSteps SteppedFlapjack.WordUnreachSteps SteppedFlapjack.LoopLiveSteps
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordUnreach
variable {width : Nat} [NeZero width]

/-- The actual Word prefix through its second dead-code pass preserves a
completed tail-entry execution and has a source-visit-based bound. -/
theorem compilerPrefix_tailEntry_secondDead_correct {C F : Type}
    (ac : AsmConfigExact width) (flag : Bool) (temp count : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : WordSteps.steps p s ≤ limit)
    (gc : gcFunConstOk s.gcFun) (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp p) = true)
    (localsRel : wordLocalsRel temp s.locals locals) (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    let q := fullSsaCcTrans count (instSelect ac temp (compileExp p))
    let out := removeDeadProg (removeUnreach (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim (removeDeadProg q)))))
    ∃ selectedLocals ssaPost finalLocals,
      evaluate out {s with locals := locals,clock := limit} = (res,{ssaPost with locals := finalLocals}) ∧
      wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = finalLocals) ∧
      WordTailEntryShape out ∧ TailEntryCodeBound out s.code K ∧
      WordSteps.steps out {s with locals := locals,clock := limit} ≤ sizeOf out * (K+1) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,deadLocals,copyRun,ssaRel,deadRel,copyShape,copyCode,_⟩ :=
    compilerPrefix_tailEntry_copy_correct ac temp count shape s post res K limit locals
      noInstallCode code run notError notTimeout sourceBound gc vars localsRel domain
  have distinct : everyInst distinctTarReg (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
      (instSelect ac temp (compileExp p)))))) = true :=
    everyInst_distinctTarReg_exact _
      (Flapjack.WordConvs.every_inst_distinct_tar_reg_copy_prop _
        (Flapjack.Compiler.Backend.WordCse.every_inst_distinct_tar_reg_word_common_subexp_elim _
          ((Flapjack.WordConvs.removeDeadProgConventions _ _ ac).2.2.2.1
            (Flapjack.WordAlloc.fullSsaCcTrans_distinctTarReg count _))))
  obtain ⟨twoRun,twoShape,twoCode,_⟩ := threeToTwo_tailEntry_correct flag copyShape
    {s with locals := locals,clock := limit} {ssaPost with locals := deadLocals} res K noInstallCode copyCode copyRun notError distinct
  obtain ⟨unreachRun,unreachShape,unreachCode,_⟩ := removeUnreach_tailEntry_correct twoShape
    {s with locals := locals,clock := limit} {ssaPost with locals := deadLocals} res K noInstallCode twoCode twoRun notError
  have ssaFlat : flatExpConventions (fullSsaCcTrans count (instSelect ac temp (compileExp p))) = true :=
    fullSsaCcTrans_flatExpConventions _ count (Flapjack.WordConvs.instSelect_flatExpConventions _ _ _)
  have deadFlat := (Flapjack.WordConvs.removeDeadProgConventions (fun _ => true) _ ac).1 ssaFlat
  have unreachFlat := Flapjack.WordConvs.flatExpConventions_removeUnreach _
    (Flapjack.WordConvs.threeToTwoRegProg_flatExpConventions flag _
      (Flapjack.WordConvs.flat_exp_conventions_copy_prop _
        (Flapjack.WordConvs.flat_exp_conventions_word_common_subexp_elim _ deadFlat)))
  obtain ⟨finalLocals,finalRun,finalRel,outShape,outCode,finalBound⟩ := removeDead_tailEntry_correct_with_steps unreachShape
    {s with locals := locals,clock := limit} {ssaPost with locals := deadLocals} res K noInstallCode unreachCode unreachFlat unreachRun notError
  refine ⟨selectedLocals,ssaPost,finalLocals,finalRun,ssaRel,?_,outShape,outCode,finalBound⟩
  cases res with
  | none => trivial
  | some r => cases r <;> simp_all only

end SteppedFlapjack.WordDeadSteps
