import SteppedFlapjack.WordCseSteps.Correct
import SteppedFlapjack.WordDeadSteps.TailEntry

/-! CSE for the generated direct tail-call entry. -/
namespace SteppedFlapjack.WordCseSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordDeadSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

/-- CSE preserves allowed direct-call destinations. -/
theorem wordCse_allowedTailEntry {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) : ∀ data, AllowedTailEntry allowed (wordCse data p).2 := by
  induction shape with
  | branch h => intro data; exact .branch (wordCse_branch h data)
  | call loc good => intro data; exact .call loc good
  | @seq a b ha hb iha ihb =>
    intro data
    simp only [wordCse]
    rcases h : wordCse data a with ⟨da,a'⟩
    rcases k : wordCse da b with ⟨db,b'⟩
    have aa := iha data
    have bb := ihb da
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb

/-- Actual CSE retains the entry shape and its original callee bound. -/
theorem cse_tailEntry_shape {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat) (bound : TailEntryCodeBound p code K) :
    WordTailEntryShape (wordCommonSubexpElim p) ∧ TailEntryCodeBound (wordCommonSubexpElim p) code K := by
  have output := wordCse_allowedTailEntry (tailEntry_allowed_of_code shape code K bound) emptyData
  exact ⟨allowedTailEntry_shape output,allowedTailEntry_calls output⟩

/-- CSE preserves a non-error execution and has a call-aware visit bound. -/
theorem cse_tailEntry_correct_with_steps {C F : Type}
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (flat : flatExpConventions p = true) (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    evaluate (wordCommonSubexpElim p) s = (res,post) ∧
    WordTailEntryShape (wordCommonSubexpElim p) ∧ TailEntryCodeBound (wordCommonSubexpElim p) s.code K ∧
    WordSteps.steps (wordCommonSubexpElim p) s ≤ sizeOf (wordCommonSubexpElim p) * (K+1) * (s.clock+1) := by
  obtain ⟨outShape,outCode⟩ := cse_tailEntry_shape shape s.code K code
  exact ⟨word_common_subexp_elim_correct p s res post ⟨run,flat,nonerror⟩,outShape,outCode,
    tailEntry_clock_bound outShape s K (tailEntry_noInstall outShape) noInstallCode outCode⟩

/-- WordSimp, selection, SSA, dead-code removal and CSE preserve a completed
entry run and bound the output visits in terms of its original limit. -/
theorem compilerPrefix_tailEntry_cse_correct {C F : Type}
    (ac : AsmConfigExact width) (temp count : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : WordSteps.steps p s ≤ limit)
    (gc : gcFunConstOk s.gcFun) (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp p) = true)
    (localsRel : wordLocalsRel temp s.locals locals) (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    let q := fullSsaCcTrans count (instSelect ac temp (compileExp p))
    let out := wordCommonSubexpElim (removeDeadProg q)
    ∃ selectedLocals ssaPost deadLocals,
      evaluate out {s with locals := locals,clock := limit} = (res,{ssaPost with locals := deadLocals}) ∧
      wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = deadLocals) ∧
      WordTailEntryShape out ∧ TailEntryCodeBound out s.code K ∧
      WordSteps.steps out {s with locals := locals,clock := limit} ≤ sizeOf out * (K+1) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,deadLocals,deadRun,ssaRel,deadRel,deadShape,deadCode,_⟩ :=
    compilerPrefix_tailEntry_removeDead_correct ac temp count shape s post res K limit locals
      noInstallCode code run notError notTimeout sourceBound gc vars localsRel domain
  have ssaFlat : flatExpConventions (fullSsaCcTrans count (instSelect ac temp (compileExp p))) = true :=
    fullSsaCcTrans_flatExpConventions _ count (Flapjack.WordConvs.instSelect_flatExpConventions _ _ _)
  have deadFlat := (Flapjack.WordConvs.removeDeadProgConventions (fun _ => true) _ ac).1 ssaFlat
  obtain ⟨cseRun,outShape,outCode,bound⟩ := cse_tailEntry_correct_with_steps deadShape
    {s with locals := locals,clock := limit} {ssaPost with locals := deadLocals} res K
    noInstallCode deadCode deadFlat deadRun notError
  refine ⟨selectedLocals,ssaPost,deadLocals,cseRun,ssaRel,?_,outShape,outCode,bound⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact deadRel

end SteppedFlapjack.WordCseSteps
