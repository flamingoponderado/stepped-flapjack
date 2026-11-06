import SteppedFlapjack.WordUnreachSteps.Program
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingle

/-! The actual compiler prefix through the optional register rewrite. -/
namespace SteppedFlapjack.WordUnreachSteps
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordDeadSteps
open SteppedFlapjack.WordCseSteps SteppedFlapjack.WordCopySteps SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordUnreach SteppedFlapjack.WordTwoRegSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- The actual Word compiler prefix through unreachable removal preserves a non-error
run and has an output visit bound computed from syntax and the source limit. -/
theorem compilerPrefix_unreach_correct (ac : AsmConfigExact width) (flag : Bool) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp p)+1)) (compileExp p) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ selectedLocals ssaPost deadLocals,
      evaluate (removeUnreach (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
        (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))))))
        {s with locals := locals,clock := limit} = (res,{ssaPost with locals := deadLocals}) ∧
      Flapjack.WordAlloc.wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = deadLocals) ∧
      steps (removeUnreach (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
          (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))))))) {s with locals := locals,clock := limit} ≤
        sizeOf (removeUnreach (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
          (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))))))) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,deadLocals,twoRun,ssaRel,deadRel,_⟩ :=
    compilerPrefix_two_correct ac flag count shape s post res locals limit run nonerror notTimeout sourceBound gc vars localRel domain
  have deadShape := removeDead_loopSequence (compilerPrefix_ssa_shape ac count shape) .ln [] []
  have cseShape := wordCse_loopSequence deadShape emptyData
  have copyShape := copyLoopSequence_shape cseShape Flapjack.Compiler.Backend.WordCopy.emptyEq
  have twoShape : LoopSequence (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim (removeDeadProg
      (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))))) := by
    cases flag with
    | false => exact copyShape
    | true => exact threeToTwo_loopSequence copyShape
  have unreach := removeUnreach_correct_with_steps twoShape {s with locals := locals,clock := limit}
    {ssaPost with locals := deadLocals} res twoRun nonerror
  refine ⟨selectedLocals,ssaPost,deadLocals,unreach.1,ssaRel,?_,unreach.2⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact deadRel

end SteppedFlapjack.WordUnreachSteps
