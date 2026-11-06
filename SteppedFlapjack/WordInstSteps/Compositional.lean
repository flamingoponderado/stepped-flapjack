import SteppedFlapjack.WordInstSteps.LoopGeneric

/-! Compositional selected-step bounds for Word programs. -/
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- A factor bounds the actual selected execution at every related state. -/
def BoundAt {width : Nat} [NeZero width] (C F : Type)
    (ac : AsmConfigExact width) (temp : Nat) (p : WordLangProgHOL (BitVec width)) (factor : Nat) : Prop :=
  ∀ (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (loc : Spt (WordLocW width)), evaluate p s = (res,post) → res ≠ some .error →
    everyVarHOL (fun x => decide (x < temp)) p = true → wordLocalsRel temp s.locals loc →
    WordSteps.steps (instSelect ac temp p) {s with locals := loc} ≤ factor * WordSteps.steps p s

/-- The quantitative induction step for sequences. -/
theorem selectedSeq_from_parts {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) (a b : WordLangProgHOL (BitVec width)) (fa fb : Nat)
    (firstBound : BoundAt C F ac temp a fa) (secondBound : BoundAt C F ac temp b fb) :
    BoundAt C F ac temp (.seq a b) (1 + fa + fb) := by
  intro s post res loc run nonerror vars localRel
  have parts := vars
  simp only [everyVarHOL, Bool.and_eq_true] at parts
  have seqEval := (evaluate_def_rebound (width := width) (C := C) (F := F )).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [seqEval] at run
  rcases firstRun : evaluate a s with ⟨firstResult,middle⟩
  rw [firstRun] at run
  have firstNonerror : firstResult ≠ some .error := by
    rintro rfl
    simp only [Prod.mk.injEq] at run
    exact nonerror run.1.symm
  obtain ⟨middleLoc,selectedFirst,firstRel⟩ :=
    inst_select_thm ac temp a s firstResult middle loc ⟨firstRun,parts.1,firstNonerror,localRel⟩
  have firstSteps := firstBound s middle firstResult loc firstRun firstNonerror parts.1 localRel
  simp only [instSelect,WordSteps.steps_seq]
  rw [selectedFirst,firstRun]
  cases firstResult with
  | none =>
    simp only at run
    have secondSteps := secondBound middle post res middleLoc run nonerror parts.2 firstRel
    simp only
    nlinarith
  | some r => simp only; nlinarith

/-- The quantitative induction step for conditionals. -/
theorem selectedIte_from_parts {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (fa fb : Nat)
    (firstBound : BoundAt C F ac temp a fa) (secondBound : BoundAt C F ac temp b fb) :
    BoundAt C F ac temp (.ite cmp r ri a b) (1 + fa + fb) := by
  intro s post res loc run nonerror vars localRel
  have parts := vars
  simp only [everyVarHOL,Bool.and_eq_true,decide_eq_true_eq] at parts
  obtain ⟨⟨⟨hr,hri⟩,ha⟩,hb⟩ := parts
  have hgv := locals_rel_get_var_simp r temp s loc ⟨hr,localRel⟩
  have hgi := locals_rel_get_var_imm_simp temp ri s loc ⟨hri,localRel⟩
  have iteEval := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [iteEval] at run
  simp only [instSelect,WordSteps.steps_ite,hgv,hgi]
  rcases hx : getVar r s with _ | x
  · simp only [hx,Prod.mk.injEq] at run
    exact (nonerror run.1.symm).elim
  rcases hy : getVarImm ri s with _ | y
  · simp only [hx,hy,Prod.mk.injEq] at run
    exact (nonerror run.1.symm).elim
  simp only [hx,hy] at run ⊢
  rcases hw : wordSemWordCmp cmp x y with _ | (_ | _)
  · simp only [hw,Prod.mk.injEq] at run
    exact (nonerror run.1.symm).elim
  · simp only [hw] at run ⊢
    have h := secondBound s post res loc run nonerror hb localRel
    have positive := WordSteps.steps_pos b s
    nlinarith
  · simp only [hw] at run ⊢
    have h := firstBound s post res loc run nonerror ha localRel
    have positive := WordSteps.steps_pos a s
    nlinarith

/-- Programs with a mechanically assembled factor, built from loop-free
expression fragments, sequencing and arbitrarily nested loops. -/
inductive BoundedProgram {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) : WordLangProgHOL (BitVec width) → Nat → Prop
  | simple {p} : SimpleProgram p → BoundedProgram ac temp p (sizeOf (instSelect ac temp p))
  | seq {a b fa fb} : BoundedProgram ac temp a fa → BoundedProgram ac temp b fb →
      BoundedProgram ac temp (.seq a b) (1 + fa + fb)
  | ite (cmp r ri) {a b fa fb} : BoundedProgram ac temp a fa → BoundedProgram ac temp b fb →
      BoundedProgram ac temp (.ite cmp r ri a b) (1 + fa + fb)
  | loop (names exitNames) {body factor} : BoundedProgram ac temp body factor →
      BoundedProgram ac temp (.loop names body exitNames) (1 + factor)

/-- The expression and control-flow program fragment. -/
inductive Program {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | assign (dst expr) : Program (.assign dst expr)
  | set (name expr) : Program (.set name expr)
  | store (expr src) : Program (.store expr src)
  | inst (i) : Program (.inst i)
  | move (priority moves) : Program (.move priority moves)
  | get (dst name) : Program (.get dst name)
  | opCurrHeap (op dst src) : Program (.opCurrHeap op dst src)
  | locValue (dst label) : Program (.locValue dst label)
  | codeBufferWrite (a b) : Program (.codeBufferWrite a b)
  | dataBufferWrite (a b) : Program (.dataBufferWrite a b)
  | ffi (index ptr len ptr2 len2 names) : Program (.ffi index ptr len ptr2 len2 names)
  | skip : Program .skip
  | tick : Program .tick
  | ret (r vs) : Program (.return r vs)
  | break (n) : Program (.break n)
  | continue (n) : Program (.continue n)
  | seq {a b} : Program a → Program b → Program (.seq a b)
  | ite (cmp r ri) {a b} : Program a → Program b → Program (.ite cmp r ri a b)
  | loop (names exitNames) {body} : Program body → Program (.loop names body exitNames)

/-- A factor computed solely from the program and instruction-selection config. -/
noncomputable def programFactor {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) : WordLangProgHOL (BitVec width) → Nat
  | .seq a b => 1 + programFactor ac temp a + programFactor ac temp b
  | .ite _ _ _ a b => 1 + programFactor ac temp a + programFactor ac temp b
  | .loop _ body _ => 1 + programFactor ac temp body
  | p => sizeOf (instSelect ac temp p)

/-- The computed factor is assembled by the quantitative proof rules. -/
theorem program_factor {width : Nat} [NeZero width] (ac : AsmConfigExact width) (temp : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : Program p) :
    BoundedProgram ac temp p (programFactor ac temp p) := by
  induction shape with
  | assign dst expr => exact .simple (.assign _ _)
  | set name expr => exact .simple (.set _ _)
  | store expr src => exact .simple (.store _ _)
  | inst i => exact .simple (.inst _)
  | move priority moves => exact .simple (.move _ _)
  | get dst name => exact .simple (.get _ _)
  | opCurrHeap op dst src => exact .simple (.opCurrHeap _ _ _)
  | locValue dst label => exact .simple (.locValue _ _)
  | codeBufferWrite a b => exact .simple (.codeBufferWrite _ _)
  | dataBufferWrite a b => exact .simple (.dataBufferWrite _ _)
  | ffi index ptr len ptr2 len2 names => exact .simple (.ffi _ _ _ _ _ _)
  | skip => exact .simple .skip
  | tick => exact .simple .tick
  | ret r vs => exact .simple (.ret _ _)
  | «break» n => exact .simple (.break _)
  | «continue» n => exact .simple (.continue _)
  | seq ha hb iha ihb => exact .seq iha ihb
  | ite cmp r ri ha hb iha ihb => exact .ite _ _ _ iha ihb
  | loop names exitNames shape ih => exact .loop _ _ ih

/-- Selected programs stay in the supported Word-to-Stack block fragment. -/
theorem boundedProgram_block {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) {p : WordLangProgHOL (BitVec width)} {factor : Nat}
    (shape : BoundedProgram ac temp p factor) : WordToStackSteps.LoopBlock (instSelect ac temp p) := by
  induction shape with
  | simple shape => exact simple_selected_block shape ac temp
  | seq ha hb iha ihb => simpa only [instSelect] using WordToStackSteps.LoopBlock.seq iha ihb
  | ite cmp r ri ha hb iha ihb => simpa only [instSelect] using WordToStackSteps.LoopBlock.ite cmp r ri iha ihb
  | loop names exitNames shape ih => simpa only [instSelect] using WordToStackSteps.LoopBlock.loop names exitNames ih

/-- The selected program is flat and cannot install code dynamically. -/
theorem boundedProgram_conventions {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) {p : WordLangProgHOL (BitVec width)} {factor : Nat}
    (shape : BoundedProgram ac temp p factor) :
    flatExpConventions (instSelect ac temp p) = true ∧ noInstallSubprogsHOL (instSelect ac temp p) = true := by
  induction shape with
  | simple shape => exact ⟨simple_selected_flat shape ac temp,simple_selected_noInstall shape ac temp⟩
  | seq ha hb iha ihb =>
    simp only [noInstallSubprogsHOL] at iha ihb ⊢
    simp only [instSelect,flatExpConventions,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨⟨iha.1,ihb.1⟩,iha.2,ihb.2⟩
  | ite cmp r ri ha hb iha ihb =>
    simp only [noInstallSubprogsHOL] at iha ihb ⊢
    simp only [instSelect,flatExpConventions,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨⟨iha.1,ihb.1⟩,iha.2,ihb.2⟩
  | loop names exitNames shape ih =>
    simpa only [instSelect,flatExpConventions,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using ih

/-- Every assembled factor is valid; subprogram bounds are derived bottom-up. -/
theorem boundedProgram_steps {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) {p : WordLangProgHOL (BitVec width)} {factor : Nat}
    (shape : BoundedProgram ac temp p factor) : BoundAt C F ac temp p factor := by
  induction shape with
  | @simple p shape =>
    intro s post res loc run nonerror vars localRel
    obtain ⟨_,_,_,_,bound⟩ := simple_selected_correct_with_steps p shape ac temp s post res loc run vars nonerror localRel
    exact bound
  | @seq a b fa fb ha hb iha ihb => exact selectedSeq_from_parts ac temp a b fa fb iha ihb
  | @ite cmp r ri a b fa fb ha hb iha ihb =>
    exact selectedIte_from_parts ac temp cmp r ri a b fa fb iha ihb
  | @loop names exitNames body factor shape ih =>
    intro s post res loc run nonerror vars localRel
    have parts := vars
    simp only [everyVarHOL,Bool.and_eq_true] at parts
    have nameVars : everyNameHOL (fun x => decide (x < temp)) (names,.ln) = true := by
      simp only [everyNameHOL,parts.1.1,Bool.true_and]
      rfl
    have bodyBound : ∀ (s post : WordSemStateFiniteExact width C F)
        (r : Option (WordSemResult width)) (loc : Spt (WordLocW width)),
        evaluate body s = (r,post) → r ≠ some .error → wordLocalsRel temp s.locals loc →
        WordSteps.steps (instSelect ac temp body) {s with locals := loc} ≤ factor * WordSteps.steps body s := by
      intro s post r loc he hn hl
      exact ih s post r loc he hn parts.1.2 hl
    simpa only [instSelect] using selectedLoop_from_body ac temp names exitNames body factor bodyBound
      parts.1.2 nameVars s post res loc run nonerror localRel

end SteppedFlapjack.WordInstSteps
