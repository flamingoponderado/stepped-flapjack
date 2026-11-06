import SteppedFlapjack.WordAllocSteps.Correct

/-! The actual Word compiler pipeline through register allocation. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordSteps
open SteppedFlapjack.WordDeadSteps SteppedFlapjack.WordCseSteps SteppedFlapjack.WordCopySteps
open SteppedFlapjack.WordTwoRegSteps SteppedFlapjack.WordUnreachSteps
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy
open Flapjack.Compiler.Backend.WordUnreach Flapjack.Compiler.Backend.WordToWord
variable {width : Nat} [NeZero width] {C F : Type}

noncomputable def preAlloc (ac : AsmConfigExact width) (flag : Bool) (count : Nat)
    (p : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  removeDeadProg (removeUnreach (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim
    (removeDeadProg (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))))))

theorem preAlloc_shape (ac : AsmConfigExact width) (flag : Bool) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) : LoopSequence (preAlloc ac flag count p) := by
  have deadShape := removeDead_loopSequence (compilerPrefix_ssa_shape ac count shape) .ln [] []
  have cseShape := wordCse_loopSequence deadShape emptyData
  have copyShape := copyLoopSequence_shape cseShape Flapjack.Compiler.Backend.WordCopy.emptyEq
  have twoShape : LoopSequence (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim (removeDeadProg
      (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))))) := by
    cases flag with
    | false => exact copyShape
    | true => exact threeToTwo_loopSequence copyShape
  exact removeDead_loopSequence (seqAssocRight_shape twoShape (.branch .skip)) .ln [] []

theorem preAlloc_cutsets (ac : AsmConfigExact width) (flag : Bool) (count : Nat)
    (p : WordLangProgHOL (BitVec width)) : wfCutsets (preAlloc ac flag count p) := by
  exact (WordConvs.removeDeadProgConventions (fun _ => true) _ ac).2.2.2.2.1
    (WordConvs.wfCutsets_removeUnreach _
      (WordConvs.threeToTwoRegProg_wfCutsets _ _
        (WordConvs.wf_cutsets_copy_prop _
          (WordConvs.wf_cutsets_word_common_subexp_elim _
            ((WordConvs.removeDeadProgConventions (fun _ => true) _ ac).2.2.2.2.1
              (fullSsaCcTrans_wfCutsets count _))))))

/-- Actual optimized and allocated Word code preserves a completed source run;
its visit bound is computed from the allocated syntax and source limit. -/
theorem compilerPrefix_alloc_correct (ac : AsmConfigExact width) (flag : Bool) (count fc alg k : Nat)
    (col : Option (Spt Nat)) {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ selectedLocals targetPost,
      evaluate (wordAlloc fc ac alg k (preAlloc ac flag count p) col)
        {s with locals := locals,clock := limit} = (res,targetPost) ∧
      wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} targetPost ∧
      steps (wordAlloc fc ac alg k (preAlloc ac flag count p) col)
        {s with locals := locals,clock := limit} ≤
        sizeOf (wordAlloc fc ac alg k (preAlloc ac flag count p) col) * (limit+1) := by
  have vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp p)+1)) (compileExp p) = true :=
    everyVarMono _ _ _ ⟨fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega,
      Flapjack.Compiler.Backend.WordAlloc.maxVarMax _⟩
  obtain ⟨selectedLocals,ssaPost,finalLocals,finalRun,ssaRel,_,_⟩ :=
    compilerPrefix_secondDead_correct ac flag count shape s post res locals limit run nonerror notTimeout sourceBound gc vars localRel domain
  obtain ⟨targetPost,targetRun,targetRel,_,targetBound⟩ := wordAlloc_correct_with_steps fc ac alg k col
    (preAlloc_shape ac flag count shape) {s with locals := locals,clock := limit}
    {ssaPost with locals := finalLocals} res finalRun nonerror
    (evenStartingLocals_of_domain locals count domain) (preAlloc_cutsets ac flag count p)
  refine ⟨selectedLocals,targetPost,targetRun,?_,targetBound⟩
  exact wordStateEqRel_trans ssaRel (wordStateEqRel_trans (wordStateEqRel_locals ssaPost finalLocals) targetRel)

/-- This fragment contains no must-terminate markers, including inside loops. -/
theorem removeMustTerminate_branch {p : WordLangProgHOL (BitVec width)} (h : Branch p) :
    Flapjack.Compiler.Backend.WordRemove.removeMustTerminate p = p := by
  induction h <;> simp_all only [Flapjack.Compiler.Backend.WordRemove.removeMustTerminate]

theorem removeMustTerminate_loopSequence {p : WordLangProgHOL (BitVec width)} (h : LoopSequence p) :
    Flapjack.Compiler.Backend.WordRemove.removeMustTerminate p = p := by
  induction h with
  | branch h => exact removeMustTerminate_branch h
  | loop names exits h => simp only [Flapjack.Compiler.Backend.WordRemove.removeMustTerminate, removeMustTerminate_branch h]
  | seq _ _ ih1 ih2 => simp only [Flapjack.Compiler.Backend.WordRemove.removeMustTerminate, ih1, ih2]

/-- The result is precisely the compiler’s full single-function output. -/
theorem fullCompileSingle_eq_alloc (ac : AsmConfigExact width) (flag : Bool) (count fc alg k : Nat)
    (col : Option (Spt Nat)) {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    fullCompileSingle flag k alg ac ((fc,count,p),col) =
      (fc,count,wordAlloc fc ac alg k (preAlloc ac flag count p) col) := by
  change (fc,count,Flapjack.Compiler.Backend.WordRemove.removeMustTerminate
    (wordAlloc fc ac alg k (preAlloc ac flag count p) col)) = _
  rw [removeMustTerminate_loopSequence (wordAlloc_loopSequence fc ac alg k col (preAlloc_shape ac flag count shape))]

end SteppedFlapjack.WordAllocSteps
