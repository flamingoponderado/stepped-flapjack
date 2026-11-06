import SteppedFlapjack.WordInstSteps.Expression

/-! Quantitative instruction selection for expression statements and control flow. -/
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordToStackSteps

/-- A Word program may evaluate expressions in assignments and stores, and use
sequences, conditional branches and ordinary control leaves. -/
inductive SimpleProgram {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | assign (dst expr) : SimpleProgram (.assign dst expr)
  | set (name expr) : SimpleProgram (.set name expr)
  | store (expr src) : SimpleProgram (.store expr src)
  | inst (i) : SimpleProgram (.inst i)
  | move (priority moves) : SimpleProgram (.move priority moves)
  | get (dst name) : SimpleProgram (.get dst name)
  | opCurrHeap (op dst src) : SimpleProgram (.opCurrHeap op dst src)
  | locValue (dst label) : SimpleProgram (.locValue dst label)
  | codeBufferWrite (a b) : SimpleProgram (.codeBufferWrite a b)
  | dataBufferWrite (a b) : SimpleProgram (.dataBufferWrite a b)
  | ffi (index ptr len ptr2 len2 names) : SimpleProgram (.ffi index ptr len ptr2 len2 names)
  | skip : SimpleProgram .skip
  | tick : SimpleProgram .tick
  | ret (r vs) : SimpleProgram (.return r vs)
  | break (n) : SimpleProgram (.break n)
  | continue (n) : SimpleProgram (.continue n)
  | seq {a b} : SimpleProgram a → SimpleProgram b → SimpleProgram (.seq a b)
  | ite (cmp r ri) {a b} : SimpleProgram a → SimpleProgram b → SimpleProgram (.ite cmp r ri a b)

/-- Instruction selection produces supported machine blocks for these programs. -/
theorem simple_selected_block {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (shape : SimpleProgram p)
    (ac : AsmConfigExact width) (temp : Nat) : LoopBlock (instSelect ac temp p) := by
  induction shape with
  | assign dst expr =>
    simp only [instSelect]
    exact selectExp_block ac dst temp (flattenExp (pullExp expr))
  | set name expr =>
    simp only [instSelect]
    exact .seq (selectExp_block ac temp temp (flattenExp (pullExp expr))) (.set _ _)
  | store expr src => exact straight_block (selectStore_straight ac temp src expr)
  | inst i => exact .inst _
  | move priority moves => exact .move _ _
  | get dst name => exact .get _ _
  | opCurrHeap op dst src => exact .opCurrHeap _ _ _
  | locValue dst label => exact .locValue _ _
  | codeBufferWrite a b => exact .codeBufferWrite _ _
  | dataBufferWrite a b => exact .dataBufferWrite _ _
  | ffi index ptr len ptr2 len2 names => exact .ffi _ _ _ _ _ _
  | skip => exact .skip
  | tick => exact .tick
  | ret r vs => exact .ret _ _
  | «break» n => exact .break _
  | «continue» n => exact .continue _
  | seq ha hb iha ihb => simpa only [instSelect] using LoopBlock.seq iha ihb
  | ite cmp r ri ha hb iha ihb => simpa only [instSelect] using LoopBlock.ite cmp r ri iha ihb

/-- Every selected expression in this fragment satisfies the backend's
flat-expression convention. -/
theorem simple_selected_flat {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (shape : SimpleProgram p)
    (ac : AsmConfigExact width) (temp : Nat) :
    flatExpConventions (instSelect ac temp p) = true := by
  induction shape with
  | assign dst expr =>
    simp only [instSelect]
    exact (straight_flat_noInstall (selectExp_straight ac dst temp (flattenExp (pullExp expr)))).1
  | set name expr =>
    simp only [instSelect,flatExpConventions,Bool.and_eq_true]
    exact ⟨(straight_flat_noInstall (selectExp_straight ac temp temp (flattenExp (pullExp expr)))).1,True.intro⟩
  | store expr src => exact (straight_flat_noInstall (selectStore_straight ac temp src expr)).1
  | inst i => rfl
  | move priority moves => rfl
  | get dst name => rfl
  | opCurrHeap op dst src => rfl
  | locValue dst label => rfl
  | codeBufferWrite a b => rfl
  | dataBufferWrite a b => rfl
  | ffi index ptr len ptr2 len2 names => rfl
  | skip => rfl
  | tick => rfl
  | ret r vs => rfl
  | «break» n => rfl
  | «continue» n => rfl
  | seq ha hb iha ihb => simp [instSelect,flatExpConventions,iha,ihb]
  | ite cmp r ri ha hb iha ihb => simp [instSelect,flatExpConventions,iha,ihb]

/-- Instruction selection introduces no dynamic installation in this fragment. -/
theorem simple_selected_noInstall {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (shape : SimpleProgram p)
    (ac : AsmConfigExact width) (temp : Nat) :
    noInstallSubprogsHOL (instSelect ac temp p) = true := by
  induction shape with
  | assign dst expr =>
    simp only [instSelect]
    exact (straight_flat_noInstall (selectExp_straight ac dst temp (flattenExp (pullExp expr)))).2
  | set name expr =>
    simp only [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_true]
    exact (straight_flat_noInstall (selectExp_straight ac temp temp (flattenExp (pullExp expr)))).2
  | store expr src => exact (straight_flat_noInstall (selectStore_straight ac temp src expr)).2
  | inst i => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | move priority moves => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | get dst name => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | opCurrHeap op dst src => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | locValue dst label => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | codeBufferWrite a b => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | dataBufferWrite a b => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | ffi index ptr len ptr2 len2 names => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | skip => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | tick => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | ret r vs => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | «break» n => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | «continue» n => simp [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | seq ha hb iha ihb =>
    simp only [noInstallSubprogsHOL] at iha ihb
    simp only [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨iha,ihb⟩
  | ite cmp r ri ha hb iha ihb =>
    simp only [noInstallSubprogsHOL] at iha ihb
    simp only [instSelect,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨iha,ihb⟩

/-- The selected program visits at most its own syntax size, independently
of the runtime state and whether a sequence terminates early. -/
theorem simple_selected_static_bound {width : Nat} [NeZero width] {C F : Type}
    {p : WordLangProgHOL (BitVec width)} (shape : SimpleProgram p)
    (ac : AsmConfigExact width) (temp : Nat) (s : WordSemStateFiniteExact width C F) :
    WordSteps.steps (instSelect ac temp p) s ≤ sizeOf (instSelect ac temp p) := by
  induction shape generalizing s with
  | assign dst expr =>
    simp only [instSelect]
    exact straight_steps_bound (selectExp_straight ac dst temp (flattenExp (pullExp expr))) s
  | set name expr =>
    simp only [instSelect]
    exact straight_steps_bound (.seq (selectExp_straight ac temp temp (flattenExp (pullExp expr))) (.setVar name temp)) s
  | store expr src => exact straight_steps_bound (selectStore_straight ac temp src expr) s
  | inst i => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf
  | move priority moves => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | get dst name => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | opCurrHeap op dst src => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | locValue dst label => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | codeBufferWrite a b => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | dataBufferWrite a b => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | ffi index ptr len ptr2 len2 names => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | skip => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf
  | tick => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf
  | ret r vs => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | «break» n => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf
  | «continue» n => simp only [instSelect]; rw [WordSteps.steps_leaf _ _ rfl]; simp_wf
  | @seq a b ha hb iha ihb =>
    simp only [instSelect,WordSteps.steps_seq]
    have hfirst := iha s
    rcases run : evaluate (instSelect ac temp a) s with ⟨res,t⟩
    cases res with
    | none =>
      have hsecond := ihb t
      simp_wf
      omega
    | some r => simp_wf; omega
  | @ite cmp r ri a b ha hb iha ihb =>
    simp only [instSelect,WordSteps.steps_ite]
    have hfirst := iha s
    have hsecond := ihb s
    rcases getVar r s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only <;> try (simp_wf; omega)
    rcases wordSemWordCmp cmp x y with _ | (_ | _) <;> simp only <;> simp_wf <;> omega

/-- The selected execution is semantically correct and bounded by a
program-dependent multiple of the separately bounded source steps. -/
theorem simple_selected_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (shape : SimpleProgram p)
    (ac : AsmConfigExact width) (temp : Nat)
    (source sourcePost : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width)) (locals : Spt (WordLocW width))
    (run : evaluate p source = (result,sourcePost))
    (vars : everyVarHOL (fun x => decide (x < temp)) p = true)
    (nonerror : result ≠ some .error) (localRel : wordLocalsRel temp source.locals locals) :
    ∃ localsPost,
      evaluate (instSelect ac temp p) {source with locals := locals} =
        (result,{sourcePost with locals := localsPost}) ∧
      (match result with
        | none | some (.break _) | some (.continue _) => wordLocalsRel temp sourcePost.locals localsPost
        | some _ => sourcePost.locals = localsPost) ∧
      LoopBlock (instSelect ac temp p) ∧
      WordSteps.steps (instSelect ac temp p) {source with locals := locals} ≤
        sizeOf (instSelect ac temp p) * WordSteps.steps p source := by
  obtain ⟨localsPost,selectedRun,selectedRel⟩ :=
    inst_select_thm ac temp p source result sourcePost locals ⟨run,vars,nonerror,localRel⟩
  refine ⟨localsPost,selectedRun,?_,simple_selected_block shape ac temp,?_⟩
  · cases result with
    | none => exact selectedRel
    | some r => cases r <;> exact selectedRel
  ·
    have bound := simple_selected_static_bound shape ac temp {source with locals := locals}
    have positive := WordSteps.steps_pos p source
    nlinarith

end SteppedFlapjack.WordInstSteps
