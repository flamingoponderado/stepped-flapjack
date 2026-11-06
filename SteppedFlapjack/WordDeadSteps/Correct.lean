import SteppedFlapjack.WordDeadSteps.Program
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead
import Flapjack.Pancake.Proofs.WordConvs.SSAFlatFull
import Flapjack.Pancake.Proofs.WordConvs.InstSelectProgram

/-! Dead-code removal correctness and its actual visit bound. -/
namespace SteppedFlapjack.WordDeadSteps
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

/-- For a non-error flat program, the actual dead-code pass preserves its
execution up to dead locals and has a syntax-and-clock visit bound. -/
theorem removeDead_correct_with_steps {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (flat : flatExpConventions p = true) (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    ∃ locals,
      evaluate (removeDeadProg p) s = (res,{post with locals := locals}) ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => post.locals = locals) ∧
      steps (removeDeadProg p) s ≤ sizeOf (removeDeadProg p) * (s.clock+1) := by
  obtain ⟨locals,run',localsRel⟩ := evaluateRemoveDeadProg p s post res ⟨flat,run,nonerror⟩
  refine ⟨locals,run',?_,removeDeadProg_clock_bound shape s⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact localsRel

/-- The actual WordSimp, selection, SSA and dead-code prefix preserves a
non-error run, with a source-relative visit bound on the final output. -/
theorem compilerPrefix_removeDead_correct (ac : AsmConfigExact width) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp p)+1)) (compileExp p) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ selectedLocals ssaPost deadLocals,
      evaluate (removeDeadProg (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))
        {s with locals := locals,clock := limit} = (res,{ssaPost with locals := deadLocals}) ∧
      Flapjack.WordAlloc.wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = deadLocals) ∧
      steps (removeDeadProg (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))
          {s with locals := locals,clock := limit} ≤
        sizeOf (removeDeadProg (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,_,ssaRun,ssaRel,_⟩ :=
    simpSelectSsa_correct_with_steps ac count shape s post res locals limit run nonerror notTimeout sourceBound gc vars localRel domain
  have flat : flatExpConventions (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))) = true :=
    fullSsaCcTrans_flatExpConventions _ count (Flapjack.WordConvs.instSelect_flatExpConventions _ _ _)
  obtain ⟨deadLocals,deadRun,deadRel,deadBound⟩ :=
    removeDead_correct_with_steps (compilerPrefix_ssa_shape ac count shape)
      {s with locals := locals,clock := limit} ssaPost res flat ssaRun nonerror
  refine ⟨selectedLocals,ssaPost,deadLocals,deadRun,ssaRel,?_,deadBound⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact deadRel

end SteppedFlapjack.WordDeadSteps
