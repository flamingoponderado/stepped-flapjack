import SteppedFlapjack.WordCseSteps.Program
import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect
import Flapjack.Pancake.Proofs.WordConvs.RemoveDead

/-! CSE semantics and a source-relative visit bound. -/
namespace SteppedFlapjack.WordCseSteps
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordDeadSteps SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

/-- CSE preserves a non-error flat execution, with an actual output-visit bound. -/
theorem cse_correct_with_steps {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (flat : flatExpConventions p = true) (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    evaluate (wordCommonSubexpElim p) s = (res,post) ∧
    steps (wordCommonSubexpElim p) s ≤ sizeOf (wordCommonSubexpElim p) * (s.clock+1) :=
  ⟨word_common_subexp_elim_correct p s res post ⟨run,flat,nonerror⟩,wordCse_clock_bound shape s⟩

/-- The actual compiler prefix through CSE preserves a completed Word run,
with an output visit bound in the original source limit. -/
theorem compilerPrefix_cse_correct (ac : AsmConfigExact width) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp p)+1)) (compileExp p) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ selectedLocals ssaPost deadLocals,
      evaluate (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
        (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))))
        {s with locals := locals,clock := limit} = (res,{ssaPost with locals := deadLocals}) ∧
      Flapjack.WordAlloc.wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = deadLocals) ∧
      steps (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
          (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))) {s with locals := locals,clock := limit} ≤
        sizeOf (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
          (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,deadLocals,deadRun,ssaRel,deadRel,_⟩ :=
    compilerPrefix_removeDead_correct ac count shape s post res locals limit run nonerror notTimeout sourceBound gc vars localRel domain
  have ssaFlat : flatExpConventions (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))) = true :=
    fullSsaCcTrans_flatExpConventions _ count (Flapjack.WordConvs.instSelect_flatExpConventions _ _ _)
  have deadFlat := (Flapjack.WordConvs.removeDeadProgConventions (fun _ => true) _ ac).1 ssaFlat
  have deadShape := removeDead_loopSequence (compilerPrefix_ssa_shape ac count shape) .ln [] []
  have cse := cse_correct_with_steps deadShape {s with locals := locals,clock := limit}
    {ssaPost with locals := deadLocals} res deadFlat deadRun nonerror
  refine ⟨selectedLocals,ssaPost,deadLocals,cse.1,ssaRel,?_,cse.2⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact deadRel

end SteppedFlapjack.WordCseSteps
