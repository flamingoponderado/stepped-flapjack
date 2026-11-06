import SteppedFlapjack.WordInstSteps.Compositional
import SteppedFlapjack.WordSimpSteps.TailTargets
import SteppedFlapjack.WordToStackSteps.CallSequence

/-! Quantitative instruction selection for direct tail-call entries. -/
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps

/-- A direct tail call has exactly the same visits after selecting its
surrounding code: the reached callee and call environment are unchanged. -/
theorem selectedTail_exact_steps {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (temp : Nat) (s : WordSemStateFiniteExact width C F) (locals : Spt (WordLocW width))
    (vars : everyVarHOL (fun x => decide (x < temp)) (.call none (some loc) [0] none : WordLangProgHOL (BitVec width)) = true)
    (rel : wordLocalsRel temp s.locals locals) :
    WordSteps.steps (.call none (some loc) [0] none) {s with locals := locals} =
      WordSteps.steps (.call none (some loc) [0] none) s := by
  have argsOk : ∀ x ∈ [0], x < temp := by
    simpa only [everyVarHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,true_and,and_true] using vars
  have argsEq := locals_rel_get_vars_simp [0] temp s locals ⟨argsOk,rel⟩
  cases hg : WordSemStateFiniteExact.getVars [0] s with
  | none =>
    rw [WordSteps.steps.eq_def,WordSteps.steps.eq_def]
    simp only [argsEq,hg]
  | some xs =>
    have hg' : WordSemStateFiniteExact.getVars [0] {s with locals := locals} = some xs := argsEq.trans hg
    cases hf : wordSemFindCode (some loc) xs s.code s.stackSize with
    | none =>
      rw [WordSteps.steps.eq_def,WordSteps.steps.eq_def]
      simp [hg,hg',wordSemBadDestArgs,wordSemAddRetLoc,hf]
    | some found =>
      obtain ⟨values,callee,ss⟩ := found
      by_cases clock : s.clock = 0
      · rw [WordSteps.steps.eq_def,WordSteps.steps.eq_def]
        simp only [hg,hg',wordSemBadDestArgs,wordSemAddRetLoc,hf]
        simp [clock]
      · have h1 := WordSteps.steps_call_tail (some loc) [0] s xs values ss callee hg
          (by simp [wordSemBadDestArgs]) hf clock
        have hf' : wordSemFindCode (some loc) xs ({s with locals := locals} : WordSemStateFiniteExact width C F).code
            ({s with locals := locals} : WordSemStateFiniteExact width C F).stackSize = some (values,callee,ss) := hf
        have h2 := WordSteps.steps_call_tail (some loc) [0] {s with locals := locals} xs values ss callee hg'
          (by simp [wordSemBadDestArgs]) hf' clock
        rw [h1,h2]
        rfl

/-- Instruction selection preserves the exact step count of a direct call. -/
theorem selectedTail_bound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp loc : Nat) :
    BoundAt C F ac temp (.call none (some loc) [0] none) 1 := by
  intro s post res locals run nonerror vars rel
  simpa only [instSelect,Nat.one_mul] using selectedTail_exact_steps loc temp s locals vars rel |>.le

/-- The entry factor is derived bottom-up from branches and the exact call
case, including the actually selected call destination. -/
theorem tailEntry_selected_bound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) : BoundAt C F ac temp p (programFactor ac temp p) := by
  induction shape with
  | branch h => exact boundedProgram_steps ac temp (program_factor ac temp (branch_program h))
  | call loc =>
    intro s post res locals run nonerror vars rel
    have h := selectedTail_exact_steps loc temp s locals vars rel
    have pos : 1 ≤ programFactor ac temp (.call none (some loc) [0] none) := by
      simp [programFactor,instSelect]
    simp only [instSelect]
    rw [h]
    nlinarith
  | @seq a b ha hb iha ihb =>
    exact selectedSeq_from_parts ac temp a b (programFactor ac temp a) (programFactor ac temp b) iha ihb

/-- Actual instruction selection puts the entry in the existing
Word-to-Stack call-sequence fragment. -/
theorem tailEntry_selected_callSequence {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) : WordToStackSteps.CallSequence (instSelect ac temp p) := by
  induction shape with
  | branch h => exact .block (boundedProgram_block ac temp (program_factor ac temp (branch_program h)))
  | call loc => exact .tail (some loc) [0]
  | seq _ _ a b => simpa only [instSelect] using WordToStackSteps.CallSequence.seq a b

/-- The selected tail entry has the flat/no-install conventions required by
the existing Word-to-Stack simulation. -/
theorem tailEntry_selected_conventions {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) :
    flatExpConventions (instSelect ac temp p) = true ∧ noInstallSubprogsHOL (instSelect ac temp p) = true := by
  induction shape with
  | branch h => exact boundedProgram_conventions ac temp (program_factor ac temp (branch_program h))
  | call loc => constructor <;> rfl
  | seq _ _ a b =>
    simp only [noInstallSubprogsHOL] at a b ⊢
    simp only [instSelect,flatExpConventions,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨⟨a.1,b.1⟩,a.2,b.2⟩

/-- WordSimp followed by actual instruction selection preserves a completed
entry execution and has a bound computed from the input visit limit. -/
theorem wordSimp_tailEntry_selected_bound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : WordSteps.steps p s ≤ limit)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < temp)) (Flapjack.Compiler.Backend.WordSimp.compileExp p) = true)
    (localsRel : wordLocalsRel temp s.locals locals) :
    let q := Flapjack.Compiler.Backend.WordSimp.compileExp p
    let normalizedPost := {post with clock := limit-(s.clock-post.clock)}
    ∃ selectedLocals,
      evaluate (instSelect ac temp q) {s with locals := locals,clock := limit} =
        (res,{normalizedPost with locals := selectedLocals}) ∧
      (match res with
        | none | some (.break _) | some (.continue _) => wordLocalsRel temp normalizedPost.locals selectedLocals
        | some _ => normalizedPost.locals = selectedLocals) ∧
      WordToStackSteps.CallSequence (instSelect ac temp q) ∧
      flatExpConventions (instSelect ac temp q) = true ∧ noInstallSubprogsHOL (instSelect ac temp q) = true ∧
      WordSteps.steps (instSelect ac temp q) {s with locals := locals,clock := limit} ≤
        programFactor ac temp q * (sizeOf q * (K+1) * (limit+1)) := by
  let q := Flapjack.Compiler.Backend.WordSimp.compileExp p
  let normalizedPost := {post with clock := limit-(s.clock-post.clock)}
  have qShape := compileExp_tailEntry shape
  obtain ⟨normalized,bound⟩ := tailEntry_wordSimp_normalized_derived shape s post res K limit
    noInstallCode code run notError notTimeout sourceBound gc
  have rel : wordLocalsRel temp ({s with clock := limit} : WordSemStateFiniteExact width C F).locals locals := localsRel
  obtain ⟨selectedLocals,selectedRun,selectedRel⟩ := inst_select_thm ac temp q
    {s with clock := limit} res normalizedPost locals ⟨normalized,vars,notError,rel⟩
  have selectedBound := tailEntry_selected_bound (C := C) (F := F) ac temp qShape
    {s with clock := limit} normalizedPost res locals normalized notError vars rel
  have conventions := tailEntry_selected_conventions ac temp qShape
  exact ⟨selectedLocals,selectedRun,selectedRel,tailEntry_selected_callSequence ac temp qShape,
    conventions.1,conventions.2,selectedBound.trans (Nat.mul_le_mul_left _ bound)⟩

end SteppedFlapjack.WordInstSteps
