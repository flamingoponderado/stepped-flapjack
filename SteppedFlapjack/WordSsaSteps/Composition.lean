import SteppedFlapjack.WordSsaSteps.Correct
import SteppedFlapjack.WordSimpSteps.LoopSequenceBound

/-! WordSimp, selection, and full SSA semantics with a source-relative bound. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordInstSteps SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- The actual WordSimp, instruction-selection and SSA prefix preserves a
non-error, non-timeout run for this fragment and bounds SSA visits by the
original source visit bound. The selected locals satisfy the SSA entry domain. -/
theorem simpSelectSsa_correct_with_steps (ac : AsmConfigExact width) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp p)+1)) (compileExp p) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ selectedLocals targetPost,
      evaluate (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))
          {s with locals := locals,clock := limit} =
        (res,{post with locals := selectedLocals,clock := limit-(s.clock-post.clock)}) ∧
      evaluate (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))
          {s with locals := locals,clock := limit} = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel
        {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} targetPost ∧
      steps (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))
          {s with locals := locals,clock := limit} ≤
        sizeOf (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))) * (limit+1) := by
  have normalized := loopSequence_wordSimp_normalized shape s post res limit run notTimeout sourceBound gc
  obtain ⟨selectedLocals,selectedRun,_⟩ :=
    inst_select_thm ac (maxVarHOL (compileExp p)+1) (compileExp p)
      {s with clock := limit} res {post with clock := limit-(s.clock-post.clock)} locals
      ⟨normalized.1,vars,nonerror,localRel⟩
  have selectedShape := select_loopSequence ac (maxVarHOL (compileExp p)+1) (compileExp_loopSequence shape)
  obtain ⟨targetPost,targetRun,rel,_,targetBound⟩ :=
    fullSsa_correct_with_steps count selectedShape {s with locals := locals,clock := limit}
      {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} res selectedRun nonerror domain
  exact ⟨selectedLocals,targetPost,selectedRun,targetRun,rel,targetBound⟩

end SteppedFlapjack.WordSsaSteps
