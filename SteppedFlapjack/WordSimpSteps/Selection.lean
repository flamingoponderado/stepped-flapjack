import SteppedFlapjack.WordSimpSteps.CompileLoop
import SteppedFlapjack.WordInstSteps.Compositional

/-! Compose the first two actual Word-to-Word passes. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.WordInstSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- The branch fragment is accepted by the existing instruction-selection
step proof. -/
theorem branch_program {p : WordLangProgHOL (BitVec width)} (shape : Branch p) : Program p := by
  induction shape with
  | assign dst e => exact .assign dst e
  | inst i => exact .inst i
  | move pri ms => exact .move pri ms
  | get dst n => exact .get dst n
  | set n e => exact .set n e
  | store e src => exact .store e src
  | skip => exact .skip
  | tick => exact .tick
  | ret r vs => exact .ret r vs
  | «break» n => exact .break n
  | «continue» n => exact .continue n
  | seq ha hb iha ihb => exact .seq iha ihb
  | ite cmp r ri ha hb iha ihb => exact .ite cmp r ri iha ihb

/-- WordSimp and instruction selection together preserve a branch execution
and multiply their independently computed visit factors. -/
theorem simp_select_branch_correct (ac : AsmConfigExact width) (temp : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : Branch p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (run : evaluate p s = (res,post))
    (nonerror : res ≠ some .error) (gc : gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp p) = true)
    (localRel : wordLocalsRel temp s.locals locals) :
    ∃ localsPost,
      evaluate (instSelect ac temp (compileExp p)) {s with locals := locals} =
        (res,{post with locals := localsPost}) ∧
      (res = none → wordLocalsRel temp post.locals localsPost) ∧
      steps (instSelect ac temp (compileExp p)) {s with locals := locals} ≤
        programFactor ac temp (compileExp p) * sizeOf (compileExp p) * steps p s := by
  have simpRun : evaluate (compileExp p) s = (res,post) := (compileExp_branch_correct shape s gc).1.trans run
  have prog := program_factor ac temp (branch_program (compileExp_branch shape))
  have selectedBound := boundedProgram_steps ac temp prog s post res locals simpRun nonerror vars localRel
  obtain ⟨localsPost,selectedRun,selectedRel⟩ := inst_select_thm ac temp (compileExp p) s res post locals
    ⟨simpRun,vars,nonerror,localRel⟩
  refine ⟨localsPost,selectedRun,?_,?_⟩
  · intro noneResult
    subst res
    exact selectedRel
  · have simpBound := compileExp_branch_steps shape s
    nlinarith

/-- The same two real passes preserve a branching loop execution and bound its
visits by factors computed from the Word program and selection configuration. -/
theorem simp_select_loop_correct (ac : AsmConfigExact width) (temp : Nat)
    (names exits : Spt Unit) {body : WordLangProgHOL (BitVec width)} (shape : Branch body)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (locals : Spt (WordLocW width)) (run : evaluate (.loop names body exits) s = (res,post))
    (nonerror : res ≠ some .error) (gc : gcFunConstOk s.gcFun)
    (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp (.loop names body exits)) = true)
    (localRel : wordLocalsRel temp s.locals locals) :
    ∃ localsPost,
      evaluate (instSelect ac temp (compileExp (.loop names body exits))) {s with locals := locals} =
        (res,{post with locals := localsPost}) ∧
      (res = none → wordLocalsRel temp post.locals localsPost) ∧
      steps (instSelect ac temp (compileExp (.loop names body exits))) {s with locals := locals} ≤
        programFactor ac temp (compileExp (.loop names body exits)) *
          (1 + sizeOf (compileExp body)) * steps (.loop names body exits) s := by
  have simpRun : evaluate (compileExp (.loop names body exits)) s = (res,post) :=
    (compileExp_loop_branch_correct names exits shape s gc).1.trans run
  have program : Program (compileExp (.loop names body exits)) := by
    rw [compileExp_loop]
    exact .loop names exits (branch_program (compileExp_branch shape))
  have prog := program_factor ac temp program
  have selectedBound := boundedProgram_steps ac temp prog s post res locals simpRun nonerror vars localRel
  obtain ⟨localsPost,selectedRun,selectedRel⟩ := inst_select_thm ac temp _ s res post locals
    ⟨simpRun,vars,nonerror,localRel⟩
  refine ⟨localsPost,selectedRun,?_,?_⟩
  · intro noneResult
    subst res
    exact selectedRel
  · have simpBound := (compileExp_loop_branch_correct names exits shape s gc).2
    nlinarith

/-- The selected output after WordSimp satisfies the structural requirements
used by the existing Word-to-Stack step theorem. -/
theorem simp_select_loop_ready (ac : AsmConfigExact width) (temp : Nat)
    (names exits : Spt Unit) {body : WordLangProgHOL (BitVec width)} (shape : Branch body) :
    WordToStackSteps.LoopBlock (instSelect ac temp (compileExp (.loop names body exits))) ∧
    flatExpConventions (instSelect ac temp (compileExp (.loop names body exits))) = true ∧
    noInstallSubprogsHOL (instSelect ac temp (compileExp (.loop names body exits))) = true := by
  have program : Program (compileExp (.loop names body exits)) := by
    rw [compileExp_loop]
    exact .loop names exits (branch_program (compileExp_branch shape))
  have derivation := program_factor ac temp program
  exact ⟨boundedProgram_block ac temp derivation, boundedProgram_conventions ac temp derivation⟩

end SteppedFlapjack.WordSimpSteps
