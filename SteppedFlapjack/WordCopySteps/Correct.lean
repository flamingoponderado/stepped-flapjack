import SteppedFlapjack.WordCopySteps.Program

/-! Composition through actual copy propagation. -/
namespace SteppedFlapjack.WordCopySteps
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordDeadSteps
open SteppedFlapjack.WordCseSteps SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

/-- The actual compiler prefix through copy propagation preserves a completed
Word run and has a source-relative bound on output visits. -/
theorem compilerPrefix_copy_correct (ac : AsmConfigExact width) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp p)+1)) (compileExp p) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ selectedLocals ssaPost deadLocals,
      evaluate (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
        (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))))
        {s with locals := locals,clock := limit} = (res,{ssaPost with locals := deadLocals}) ∧
      Flapjack.WordAlloc.wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = deadLocals) ∧
      steps (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
          (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))))) {s with locals := locals,clock := limit} ≤
        sizeOf (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
          (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))))) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,deadLocals,cseRun,ssaRel,deadRel,_⟩ :=
    compilerPrefix_cse_correct ac count shape s post res locals limit run nonerror notTimeout sourceBound gc vars localRel domain
  have deadShape := removeDead_loopSequence (compilerPrefix_ssa_shape ac count shape) .ln [] []
  have cseShape := wordCse_loopSequence deadShape emptyData
  have copy := copyProp_correct_with_steps cseShape {s with locals := locals,clock := limit}
    {ssaPost with locals := deadLocals} res cseRun nonerror
  refine ⟨selectedLocals,ssaPost,deadLocals,copy.1,ssaRel,?_,copy.2⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact deadRel

end SteppedFlapjack.WordCopySteps
