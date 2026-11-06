import SteppedFlapjack.WordCopySteps.Correct
import SteppedFlapjack.WordCseSteps.TailEntry

/-! Copy propagation for the generated direct tail-call entry. -/
namespace SteppedFlapjack.WordCopySteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordDeadSteps
open SteppedFlapjack.WordCseSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

/-- Copy propagation preserves allowed direct-call destinations. -/
theorem copy_allowedTailEntry {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) : ∀ cs, AllowedTailEntry allowed (copyPropProg p cs).1 := by
  induction shape with
  | branch h => intro cs; exact .branch (copyBranch_shape h cs)
  | call loc good => intro cs; exact .call loc good
  | @seq a b ha hb iha ihb =>
    intro cs
    simp only [copyPropProg]
    rcases h : copyPropProg a cs with ⟨a',ca⟩
    rcases k : copyPropProg b ca with ⟨b',cb⟩
    have aa := iha cs
    have bb := ihb ca
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb

/-- Copy propagation preserves a non-error entry execution and its callee
bound, with a syntax-and-clock bound on output visits. -/
theorem copy_tailEntry_correct_with_steps {C F : Type}
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    evaluate (copyProp p) s = (res,post) ∧
    WordTailEntryShape (copyProp p) ∧ TailEntryCodeBound (copyProp p) s.code K ∧
    WordSteps.steps (copyProp p) s ≤ sizeOf (copyProp p) * (K+1) * (s.clock+1) := by
  have output := copy_allowedTailEntry (tailEntry_allowed_of_code shape s.code K code) emptyEq
  have outShape : WordTailEntryShape (copyProp p) := allowedTailEntry_shape output
  have outCode : TailEntryCodeBound (copyProp p) s.code K := allowedTailEntry_calls output
  have noerror : (evaluate p s).1 ≠ some .error := by rw [run]; exact nonerror
  exact ⟨(evaluateCopyProp noerror).trans run,outShape,outCode,
    tailEntry_clock_bound outShape s K (tailEntry_noInstall outShape) noInstallCode outCode⟩

/-- The actual compiler prefix through copy propagation preserves the entry
execution and has a source-visit-based bound. -/
theorem compilerPrefix_tailEntry_copy_correct {C F : Type}
    (ac : AsmConfigExact width) (temp count : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : WordSteps.steps p s ≤ limit)
    (gc : gcFunConstOk s.gcFun) (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp p) = true)
    (localsRel : wordLocalsRel temp s.locals locals) (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    let q := fullSsaCcTrans count (instSelect ac temp (compileExp p))
    let out := copyProp (wordCommonSubexpElim (removeDeadProg q))
    ∃ selectedLocals ssaPost deadLocals,
      evaluate out {s with locals := locals,clock := limit} = (res,{ssaPost with locals := deadLocals}) ∧
      wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = deadLocals) ∧
      WordTailEntryShape out ∧ TailEntryCodeBound out s.code K ∧
      WordSteps.steps out {s with locals := locals,clock := limit} ≤ sizeOf out * (K+1) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,deadLocals,cseRun,ssaRel,deadRel,cseShape,cseCode,_⟩ :=
    compilerPrefix_tailEntry_cse_correct ac temp count shape s post res K limit locals
      noInstallCode code run notError notTimeout sourceBound gc vars localsRel domain
  obtain ⟨copyRun,outShape,outCode,bound⟩ := copy_tailEntry_correct_with_steps cseShape
    {s with locals := locals,clock := limit} {ssaPost with locals := deadLocals} res K
    noInstallCode cseCode cseRun notError
  refine ⟨selectedLocals,ssaPost,deadLocals,copyRun,ssaRel,?_,outShape,outCode,bound⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact deadRel

end SteppedFlapjack.WordCopySteps
