import SteppedFlapjack.WordSsaSteps.Selection
import SteppedFlapjack.WordInstSteps.TailEntry
import SteppedFlapjack.WordSsaSteps.Correct

/-! Actual selection and SSA preserve direct tail-entry calls. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width]

/-- Instruction selection keeps the direct call and supported branches. -/
theorem select_tailEntry (ac : AsmConfigExact width) (temp : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p) :
    WordTailEntryShape (instSelect ac temp p) := by
  induction shape with
  | branch h => exact .branch (select_branch ac temp h)
  | call loc => exact .call loc
  | seq _ _ a b => simpa only [instSelect] using WordTailEntryShape.seq a b

/-- SSA inserts argument moves but retains the direct destination and the
single return-location argument. -/
theorem ssa_tailEntry {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p) :
    ∀ ssa next targets, WordTailEntryShape (ssaCcTrans p ssa next targets).1 := by
  induction shape with
  | branch h => intro ssa next targets; exact .branch (ssaBranch_shape h ssa next targets)
  | call loc =>
    intro ssa next targets
    simp only [ssaCcTrans,List.map_cons,List.map_nil,List.length_cons,List.length_nil]
    exact .seq (.branch (.move _ _)) (.call loc)
  | @seq a b ha hb iha ihb =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : ssaCcTrans a ssa next targets with ⟨a',sa,na⟩
    rcases k : ssaCcTrans b sa na targets with ⟨b',sb,nb⟩
    have aa := iha ssa next targets
    have bb := ihb sa na targets
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb

/-- The full SSA pass retains the direct-call entry shape. -/
theorem fullSsa_tailEntry (count : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) : WordTailEntryShape (fullSsaCcTrans count p) := by
  unfold fullSsaCcTrans setupSSA
  dsimp only
  rcases h : listNextVarRename (evenList count) .ln (limitVar p) with ⟨newNames,ssa,next⟩
  rcases k : ssaCcTrans p ssa next [] with ⟨body,sa,na⟩
  have hb := ssa_tailEntry shape ssa next []
  simp only [k] at hb
  exact .seq (.branch (.move _ _)) hb

/-- Selection keeps every direct-call destination within the input set. -/
theorem select_allowedTailEntry (ac : AsmConfigExact width) (temp : Nat) {allowed : Nat → Prop}
    {p : WordLangProgHOL (BitVec width)} (shape : AllowedTailEntry allowed p) :
    AllowedTailEntry allowed (instSelect ac temp p) := by
  induction shape with
  | branch h => exact .branch (select_branch ac temp h)
  | call loc good => exact .call loc good
  | seq _ _ a b => simpa only [instSelect] using AllowedTailEntry.seq a b

/-- SSA argument shuffling introduces no new tail-call destination. -/
theorem ssa_allowedTailEntry {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) :
    ∀ ssa next targets, AllowedTailEntry allowed (ssaCcTrans p ssa next targets).1 := by
  induction shape with
  | branch h => intro ssa next targets; exact .branch (ssaBranch_shape h ssa next targets)
  | call loc good =>
    intro ssa next targets
    simp only [ssaCcTrans,List.map_cons,List.map_nil,List.length_cons,List.length_nil]
    exact .seq (.branch (.move _ _)) (.call loc good)
  | @seq a b ha hb iha ihb =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : ssaCcTrans a ssa next targets with ⟨a',sa,na⟩
    rcases k : ssaCcTrans b sa na targets with ⟨b',sb,nb⟩
    have aa := iha ssa next targets
    have bb := ihb sa na targets
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb

/-- Full SSA preserves the input call destinations. -/
theorem fullSsa_allowedTailEntry (count : Nat) {allowed : Nat → Prop}
    {p : WordLangProgHOL (BitVec width)} (shape : AllowedTailEntry allowed p) :
    AllowedTailEntry allowed (fullSsaCcTrans count p) := by
  unfold fullSsaCcTrans setupSSA
  dsimp only
  rcases h : listNextVarRename (evenList count) .ln (limitVar p) with ⟨newNames,ssa,next⟩
  rcases k : ssaCcTrans p ssa next [] with ⟨body,sa,na⟩
  have hb := ssa_allowedTailEntry shape ssa next []
  simp only [k] at hb
  exact .seq (.branch (.move _ _)) hb

/-- The actual WordSimp, instruction-selection and SSA pipeline retains
callee bounds derived for its input call destinations. -/
theorem compilerPrefix_tailEntry_codeBound (ac : AsmConfigExact width) (temp count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat) (bound : TailEntryCodeBound p code K) :
    TailEntryCodeBound (fullSsaCcTrans count (instSelect ac temp (Flapjack.Compiler.Backend.WordSimp.compileExp p))) code K := by
  have initial := tailEntry_allowed_of_code shape code K bound
  have output := fullSsa_allowedTailEntry count (select_allowedTailEntry ac temp (compileExp_allowedTailEntry initial))
  exact allowedTailEntry_calls output

/-- The real compiler prefix has a syntax-and-clock bound, depending only on
its own call destinations' callee bounds. -/
theorem compilerPrefix_tailEntry_clock_bound {C F : Type} (ac : AsmConfigExact width) (temp count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s : WordSemStateFiniteExact width C F) (K : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (bound : TailEntryCodeBound p s.code K) :
    let out := fullSsaCcTrans count (instSelect ac temp (Flapjack.Compiler.Backend.WordSimp.compileExp p))
    WordSteps.steps out s ≤ sizeOf out * (K+1) * (s.clock+1) := by
  have outShape := fullSsa_tailEntry count (select_tailEntry ac temp (compileExp_tailEntry shape))
  exact tailEntry_clock_bound outShape s K (tailEntry_noInstall outShape) noInstallCode
    (compilerPrefix_tailEntry_codeBound ac temp count shape s.code K bound)

/-- A direct call into a supported callee does not inspect or change the
permutation oracle. -/
theorem directTail_withPermute {C F : Type} (loc : Nat) (callee : WordLangProgHOL (BitVec width))
    (calleeShape : LoopSequence callee) (s : WordSemStateFiniteExact width C F)
    (perm : Nat → Nat → Nat) (lookup : sptLookup loc s.code = some (1,callee)) :
    WordSemStateFiniteExact.evaluate (.call none (some loc) [0] none) {s with permute := perm} =
      ((WordSemStateFiniteExact.evaluate (.call none (some loc) [0] none) s).1,
       {(WordSemStateFiniteExact.evaluate (.call none (some loc) [0] none) s).2 with permute := perm}) := by
  rw [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.evaluate]
  cases hv : WordSemStateFiniteExact.getVar 0 s with
  | none =>
    simp only [WordSemStateFiniteExact.getVar] at hv
    simp [WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,hv]
  | some v =>
    have hv' : WordSemStateFiniteExact.getVar 0 {s with permute := perm} = some v := hv
    simp only [WordSemStateFiniteExact.getVars,hv,hv',wordSemBadDestArgs,wordSemAddRetLoc,
      wordSemFindCode,lookup,List.length_cons,List.length_nil,if_true]
    by_cases clock : s.clock = 0
    · simp [clock,WordSemStateFiniteExact.flushState]
    · simp only [clock,↓reduceDIte]
      have changePerm : WordSemStateFiniteExact.callEnv [v] (sptLookup loc s.stackSize)
          (WordSemStateFiniteExact.decClock {s with permute := perm}) =
        {WordSemStateFiniteExact.callEnv [v] (sptLookup loc s.stackSize)
          (WordSemStateFiniteExact.decClock s) with permute := perm} := rfl
      rw [changePerm,loopSequence_withPermute calleeShape]
      cases hr : WordSemStateFiniteExact.evaluate callee
          (WordSemStateFiniteExact.callEnv [v] (sptLookup loc s.stackSize) (WordSemStateFiniteExact.decClock s)) with
      | mk r post =>
        cases bad : wordSemBadFunReturn r <;> simp_all

/-- A tail-entry sequence and its reached supported callees are independent of
the permutation oracle, without constraining unrelated code bodies. -/
theorem tailEntry_withPermute {C F : Type} {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) :
    ∀ (s : WordSemStateFiniteExact width C F) (perm : Nat → Nat → Nat) (K : Nat),
      WordProps.noInstallCode s.code → TailEntryCodeBound p s.code K →
      WordSemStateFiniteExact.evaluate p {s with permute := perm} =
        ((WordSemStateFiniteExact.evaluate p s).1,{(WordSemStateFiniteExact.evaluate p s).2 with permute := perm}) := by
  induction shape with
  | branch h => intro s perm K _ _; exact branch_withPermute h s perm
  | call loc =>
    intro s perm K _ code
    obtain ⟨callee,lookup,shape,_⟩ := code loc (.call loc)
    exact directTail_withPermute loc callee shape s perm lookup
  | @seq a b ha hb iha ihb =>
    intro s perm K noInstallCode code
    have ca : TailEntryCodeBound a s.code K := fun loc h => code loc (.left h)
    have cb : TailEntryCodeBound b s.code K := fun loc h => code loc (.right h)
    have first := iha s perm K noInstallCode ca
    have preserved := WordSemStateFiniteExact.code_evaluate a s (tailEntry_noInstall ha) noInstallCode
    rw [WordSemStateFiniteExact.evaluate_seq_eq,WordSemStateFiniteExact.evaluate_seq_eq,first]
    rcases run : WordSemStateFiniteExact.evaluate a s with ⟨out,middle⟩
    rw [run] at preserved
    simp only at preserved
    cases out with
    | none =>
      exact ihb middle perm K (by simpa only [preserved] using noInstallCode)
        (by simpa only [preserved] using cb)
    | some r => rfl

/-- Actual full SSA preserves a completed tail-entry run and has a
syntax-and-clock visit bound using the input's call-target code facts. -/
theorem fullSsa_tailEntry_correct_with_steps {C F : Type} (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : WordSemStateFiniteExact.evaluate p s = (res,post)) (nonerror : res ≠ some .error)
    (domain : sptDomain s.locals = (fun key => key ∈ evenList count)) :
    ∃ targetPost,
      WordSemStateFiniteExact.evaluate (fullSsaCcTrans count p) s = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel post targetPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => post.locals = targetPost.locals) ∧
      WordSteps.steps (fullSsaCcTrans count p) s ≤ sizeOf (fullSsaCcTrans count p) * (K+1) * (s.clock+1) := by
  obtain ⟨perm,correct⟩ := fullSsaCcTransCorrect p s count domain
  have permRun := tailEntry_withPermute shape s perm K noInstallCode code
  rw [run] at permRun
  simp only at permRun
  have permNonerror : (WordSemStateFiniteExact.evaluate p {s with permute := perm}).1 ≠ some .error := by
    rw [permRun]; exact nonerror
  dsimp only at correct
  rw [if_neg permNonerror,permRun] at correct
  rcases targetRun : WordSemStateFiniteExact.evaluate (fullSsaCcTrans count p) s with ⟨targetResult,targetPost⟩
  simp only [targetRun] at correct
  have outShape := fullSsa_tailEntry count shape
  have allowed := tailEntry_allowed_of_code shape s.code K code
  have outCode : TailEntryCodeBound (fullSsaCcTrans count p) s.code K :=
    allowedTailEntry_calls (fullSsa_allowedTailEntry count allowed)
  have bound := tailEntry_clock_bound outShape s K (tailEntry_noInstall outShape) noInstallCode outCode
  refine ⟨targetPost,?_,?_,?_,bound⟩
  · exact congrArg (fun r => (r,targetPost)) correct.1.symm
  · simpa only [Flapjack.WordAlloc.wordStateEqRel] using correct.2.1
  · cases res with
    | none => trivial
    | some r => cases r <;> exact correct.2.2

/-- WordSimp, instruction selection and full SSA execute the completed
entry, with a visit bound computed from its original Word visit limit. -/
theorem simpSelectSsa_tailEntry_correct_with_steps {C F : Type}
    (ac : AsmConfigExact width) (temp count : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : WordSemStateFiniteExact.evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : WordSteps.steps p s ≤ limit)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < temp)) (Flapjack.Compiler.Backend.WordSimp.compileExp p) = true)
    (localsRel : wordLocalsRel temp s.locals locals) (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    let q := instSelect ac temp (Flapjack.Compiler.Backend.WordSimp.compileExp p)
    ∃ selectedLocals targetPost,
      WordSemStateFiniteExact.evaluate (fullSsaCcTrans count q) {s with locals := locals,clock := limit} = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel
        {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} targetPost ∧
      WordTailEntryShape (fullSsaCcTrans count q) ∧
      WordSteps.steps (fullSsaCcTrans count q) {s with locals := locals,clock := limit} ≤
        sizeOf (fullSsaCcTrans count q) * (K+1) * (limit+1) := by
  let simpProg := Flapjack.Compiler.Backend.WordSimp.compileExp p
  let selected := instSelect ac temp simpProg
  obtain ⟨selectedLocals,selectedRun,_,_,_,_,_⟩ :=
    WordInstSteps.wordSimp_tailEntry_selected_bound ac temp shape s post res K limit locals
      noInstallCode code run notError notTimeout sourceBound gc vars localsRel
  have selectedShape := select_tailEntry ac temp (compileExp_tailEntry shape)
  have allowed := select_allowedTailEntry ac temp (compileExp_allowedTailEntry (tailEntry_allowed_of_code shape s.code K code))
  have selectedCode : TailEntryCodeBound selected s.code K := allowedTailEntry_calls allowed
  obtain ⟨targetPost,targetRun,rel,_,bound⟩ := fullSsa_tailEntry_correct_with_steps count selectedShape
    {s with locals := locals,clock := limit} {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)}
    res K noInstallCode selectedCode selectedRun notError domain
  exact ⟨selectedLocals,targetPost,targetRun,rel,fullSsa_tailEntry count selectedShape,bound⟩

end SteppedFlapjack.WordSsaSteps
