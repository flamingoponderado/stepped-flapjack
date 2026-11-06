import SteppedFlapjack.WordInstSteps.Simple

/-! Quantitative instruction selection for Word loops. -/
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- A loop with a loop-free expression body has a selected step count bounded
by a program-dependent multiple of its source step count. -/
theorem selectedLoop_steps_bound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width)) (shape : SimpleProgram body)
    (bodyVars : everyVarHOL (fun x => decide (x < temp)) body = true)
    (nameVars : everyNameHOL (fun x => decide (x < temp)) (names,.ln) = true)
    (source sourcePost : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width)) (locals : Spt (WordLocW width))
    (run : evaluate (.loop names body exitNames) source = (result,sourcePost))
    (nonerror : result ≠ some .error) (localRel : wordLocalsRel temp source.locals locals) :
    WordSteps.steps (.loop names (instSelect ac temp body) exitNames) {source with locals := locals} ≤
      (1 + sizeOf (instSelect ac temp body)) * WordSteps.steps (.loop names body exitNames) source := by
  induction hc : source.clock using Nat.strongRecOn generalizing source sourcePost result locals with
  | _ clock ih =>
    have loopEval := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [loopEval] at run
    rcases cut : wordSemCutEnv (names,.ln) source.locals with _ | env
    · have cutSource : cutState (names,.ln) source = none := by unfold cutState; rw [cut]
      rw [cutSource] at run
      simp only [Prod.mk.injEq] at run
      exact (nonerror run.1.symm).elim
    have cutTarget := locals_rel_cut_env temp source.locals locals (names,.ln) env ⟨localRel,nameVars,cut⟩
    have cutSource : cutState (names,.ln) source = some {source with locals := env} := by
      unfold cutState; rw [cut]
    have cutTargetState : cutState (names,.ln) {source with locals := locals} = some {source with locals := env} := by
      unfold cutState
      simp only [cutTarget]
    rw [cutSource] at run
    simp only at run
    rcases bodyRun : evaluate body {source with locals := env} with ⟨bodyResult,post⟩
    rw [bodyRun] at run
    have bodyNotError : bodyResult ≠ some .error := by
      rintro rfl
      simp [wordSemContLoop,wordSemExitLoop] at run
      exact nonerror run.1.symm
    obtain ⟨postLocals,selectedRun,selectedRel⟩ :=
      inst_select_thm ac temp body {source with locals := env} bodyResult post env
        ⟨bodyRun,bodyVars,bodyNotError,fun _ _ => rfl⟩
    have selectedRun' : evaluate (instSelect ac temp body) {source with locals := env} =
        (bodyResult,{post with locals := postLocals}) := selectedRun
    simp only [← hc] at *
    rw [WordSteps.steps_loop,WordSteps.steps_loop,cutSource,cutTargetState]
    simp only
    rw [bodyRun,selectedRun']
    have selectedBody := simple_selected_static_bound shape ac temp {source with locals := env}
    have sourceBody := WordSteps.steps_pos body {source with locals := env}
    by_cases cont : wordSemContLoop bodyResult ∧ post.clock ≠ 0
    · have contBool : wordSemContLoop bodyResult = true := cont.1
      have postLocalRel : wordLocalsRel temp post.locals postLocals := by
        rcases bodyResult with _ | (_ | _ | _ | (_ | n) | _ | _ | _ | _) <;>
          simp [wordSemContLoop] at contBool <;> exact selectedRel
      have nextRun : evaluate (.loop names body exitNames) (decClock post) = (result,sourcePost) := by
        simp only [contBool,if_true] at run
        simp only [cont.2,if_false] at run
        simpa only [wordSemSTOP] using run
      have hclock := evaluate_clock body {source with locals := env} bodyResult post bodyRun
      have smaller : (decClock post).clock < source.clock := by
        simp only [decClock] at hclock ⊢
        omega
      have rest := ih _ smaller (decClock post) sourcePost result postLocals nextRun nonerror postLocalRel rfl
      simp only [cont.1, true_and, decClock]
      simp only [if_pos cont.2]
      simp only [decClock] at rest
      nlinarith
    · simp only [cont,if_false]
      nlinarith

/-- The original instruction-selection correctness theorem and the proved
iteration-sensitive bound, with the loop body supplied by the loop-free fragment. -/
theorem selectedLoop_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width)) (shape : SimpleProgram body)
    (source sourcePost : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width)) (locals : Spt (WordLocW width))
    (run : evaluate (.loop names body exitNames) source = (result,sourcePost))
    (vars : everyVarHOL (fun x => decide (x < temp)) (.loop names body exitNames) = true)
    (nonerror : result ≠ some .error) (localRel : wordLocalsRel temp source.locals locals) :
    ∃ postLocals,
      evaluate (instSelect ac temp (.loop names body exitNames)) {source with locals := locals} =
        (result,{sourcePost with locals := postLocals}) ∧
      (match result with
        | none | some (.break _) | some (.continue _) => wordLocalsRel temp sourcePost.locals postLocals
        | some _ => sourcePost.locals = postLocals) ∧
      WordSteps.steps (instSelect ac temp (.loop names body exitNames)) {source with locals := locals} ≤
        (1 + sizeOf (instSelect ac temp body)) * WordSteps.steps (.loop names body exitNames) source := by
  obtain ⟨postLocals,selectedRun,selectedRel⟩ :=
    inst_select_thm ac temp (.loop names body exitNames) source result sourcePost locals
      ⟨run,vars,nonerror,localRel⟩
  have parts := vars
  simp only [everyVarHOL, Bool.and_eq_true] at parts
  have nameVars : everyNameHOL (fun x => decide (x < temp)) (names,.ln) = true := by
    simp only [everyNameHOL,parts.1.1,Bool.true_and]
    rfl
  refine ⟨postLocals,selectedRun,?_,?_⟩
  · cases result with
    | none => exact selectedRel
    | some r => cases r <;> exact selectedRel
  · simpa only [instSelect] using selectedLoop_steps_bound ac temp names exitNames body shape
      parts.1.2 nameVars source sourcePost result locals run nonerror localRel

end SteppedFlapjack.WordInstSteps
