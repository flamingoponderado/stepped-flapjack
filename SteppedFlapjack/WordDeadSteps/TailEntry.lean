import SteppedFlapjack.WordDeadSteps.Correct
import SteppedFlapjack.WordSsaSteps.TailEntry

/-! Dead-code removal for generated direct tail-call entries. -/
namespace SteppedFlapjack.WordDeadSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

omit [NeZero width] in
theorem compactSeq_allowedTailEntry {allowed : Nat → Prop} {a b : WordLangProgHOL (BitVec width)}
    (ha : AllowedTailEntry allowed a) (hb : AllowedTailEntry allowed b) :
    AllowedTailEntry allowed (match a,b with | .skip,_ => b | _,.skip => a | _,_ => .seq a b) := by
  cases a <;> cases b <;> first | exact ha | exact hb | exact .seq ha hb

/-- Dead-code elimination preserves supported branches and never introduces a
new direct-call destination. -/
theorem removeDead_allowedTailEntry {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) :
    ∀ live nlive targets, AllowedTailEntry allowed (removeDead p live nlive targets).1 := by
  induction shape with
  | branch hp => intro live nlive targets; exact .branch (removeDead_branch hp live nlive targets)
  | call loc good => intro live nlive targets; simpa only [removeDead] using AllowedTailEntry.call loc good
  | @seq a b ha hb iha ihb =>
    intro live nlive targets
    simp only [removeDead]
    rcases h : removeDead b live nlive targets with ⟨b',lb,nb⟩
    rcases k : removeDead a lb nb targets with ⟨a',la,na⟩
    have aa := iha lb nb targets
    have bb := ihb live nlive targets
    simp only [h] at bb
    simp only [k] at aa
    exact compactSeq_allowedTailEntry aa bb

omit [NeZero width] in
theorem allowedTailEntry_shape {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) : WordTailEntryShape p := by
  induction shape with
  | branch h => exact .branch h
  | call loc _ => exact .call loc
  | seq _ _ a b => exact .seq a b

/-- The actual dead-code pass preserves the entry shape and its callee bound. -/
theorem removeDeadProg_tailEntry {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat) (bound : TailEntryCodeBound p code K) :
    WordTailEntryShape (removeDeadProg p) ∧ TailEntryCodeBound (removeDeadProg p) code K := by
  have initial := tailEntry_allowed_of_code shape code K bound
  have output := removeDead_allowedTailEntry initial .ln [] []
  exact ⟨allowedTailEntry_shape output,allowedTailEntry_calls output⟩

/-- Dead-code removal preserves a non-error tail-entry execution and has a
clock bound using only its original direct call destinations. -/
theorem removeDead_tailEntry_correct_with_steps {C F : Type}
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (flat : flatExpConventions p = true) (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    ∃ locals, evaluate (removeDeadProg p) s = (res,{post with locals := locals}) ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => post.locals = locals) ∧
      WordTailEntryShape (removeDeadProg p) ∧ TailEntryCodeBound (removeDeadProg p) s.code K ∧
      WordSteps.steps (removeDeadProg p) s ≤ sizeOf (removeDeadProg p) * (K+1) * (s.clock+1) := by
  obtain ⟨locals,run',localsRel⟩ := evaluateRemoveDeadProg p s post res ⟨flat,run,nonerror⟩
  obtain ⟨outShape,outCode⟩ := removeDeadProg_tailEntry shape s.code K code
  have steps := tailEntry_clock_bound outShape s K (tailEntry_noInstall outShape) noInstallCode outCode
  refine ⟨locals,run',?_,outShape,outCode,steps⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact localsRel

/-- The actual WordSimp, selection, SSA and dead-code prefix preserves a
completed entry execution and has a source-visit-based bound. -/
theorem compilerPrefix_tailEntry_removeDead_correct {C F : Type}
    (ac : AsmConfigExact width) (temp count : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : WordSteps.steps p s ≤ limit)
    (gc : gcFunConstOk s.gcFun) (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp p) = true)
    (localsRel : wordLocalsRel temp s.locals locals) (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    let q := fullSsaCcTrans count (instSelect ac temp (compileExp p))
    let out := removeDeadProg q
    ∃ selectedLocals ssaPost deadLocals,
      evaluate out {s with locals := locals,clock := limit} = (res,{ssaPost with locals := deadLocals}) ∧
      wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} ssaPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => ssaPost.locals = deadLocals) ∧
      WordTailEntryShape out ∧ TailEntryCodeBound out s.code K ∧
      WordSteps.steps out {s with locals := locals,clock := limit} ≤ sizeOf out * (K+1) * (limit+1) := by
  obtain ⟨selectedLocals,ssaPost,ssaRun,ssaRel,ssaShape,_⟩ :=
    simpSelectSsa_tailEntry_correct_with_steps ac temp count shape s post res K limit locals
      noInstallCode code run notError notTimeout sourceBound gc vars localsRel domain
  have ssaCode := compilerPrefix_tailEntry_codeBound ac temp count shape s.code K code
  have flat : flatExpConventions (fullSsaCcTrans count (instSelect ac temp (compileExp p))) = true :=
    fullSsaCcTrans_flatExpConventions _ count (Flapjack.WordConvs.instSelect_flatExpConventions _ _ _)
  obtain ⟨deadLocals,deadRun,deadRel,outShape,outCode,bound⟩ :=
    removeDead_tailEntry_correct_with_steps ssaShape {s with locals := locals,clock := limit} ssaPost res K
      noInstallCode ssaCode flat ssaRun notError
  refine ⟨selectedLocals,ssaPost,deadLocals,deadRun,ssaRel,?_,outShape,outCode,bound⟩
  cases res with
  | none => trivial
  | some r => cases r <;> exact deadRel

end SteppedFlapjack.WordDeadSteps
