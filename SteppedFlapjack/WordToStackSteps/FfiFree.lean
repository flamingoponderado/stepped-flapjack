import SteppedFlapjack.LabToTargetSteps.FfiFreeFlatten
import SteppedFlapjack.WordToStackSteps.BitmapFree
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopInstructions

/-! FFI-free Word fragments remain FFI-free under native compilation. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.LabToTargetSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps

theorem wMoveAux_noFfi {width : Nat} [NeZero width]
    (xs : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    stackNoFfi (wMoveAuxNative xs kf : HolProg width) = true := by
  have single (xy : Sum Nat Nat × Sum Nat Nat) :
      stackNoFfi (wMoveSingleNative (width := width) xy kf) = true := by
    rcases xy with ⟨x, y⟩
    cases x <;> cases y <;> rfl
  induction xs with
  | nil => rfl
  | cons xy rest ih =>
      cases rest with
      | nil => exact single xy
      | cons next tail => simp only [wMoveAuxNative, stackNoFfi, single, ih, Bool.true_and]

theorem wStackLoad_noFfi {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (prog : HolProg width) :
    stackNoFfi (wStackLoadNative loads prog) = stackNoFfi prog := by
  induction loads with
  | nil => rfl
  | cons load rest ih => simp [wStackLoadNative, stackNoFfi, ih]

theorem wRegWrite1_noFfi {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, stackNoFfi (prog reg) = true) :
    stackNoFfi (wRegWrite1Native prog r kf) = true := by
  by_cases reg : r / 2 < kf.1 <;> simp [wRegWrite1Native, reg, stackNoFfi, h]

theorem wRegWrite2_noFfi {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, stackNoFfi (prog reg) = true) :
    stackNoFfi (wRegWrite2Native prog r kf) = true := by
  by_cases reg : r / 2 < kf.1 <;> simp [wRegWrite2Native, reg, stackNoFfi, h]

theorem wInst_noFfi {width : Nat} [NeZero width]
    (instruction : HolInst width) (frame : Nat × Nat × Nat) :
    stackNoFfi (wInstNative instruction frame) = true := by
  have write1 (g : Nat → HolInst width) (r : Nat) :
      stackNoFfi (wRegWrite1Native (fun reg => .inst (g reg)) r frame) = true :=
    wRegWrite1_noFfi _ r frame (fun _ => rfl)
  cases instruction with
  | arith a =>
    cases a <;> try (rename_i op d s ri; cases ri)
    all_goals simp [wInstNative, wStackLoad_noFfi, write1, stackNoFfi]
  | mem op d addr =>
    cases addr
    cases op <;> simp [wInstNative, wStackLoad_noFfi,
      write1, stackNoFfi]
  | skip => rfl
  | const n c => simp [wInstNative, write1]


/-- Native compilation of a branch emits no Stack FFI instruction. -/
theorem branch_compNative_noFfi {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) {p : WordLangProgHOL (BitVec width)}
    (shape : Branch p) : ∀ bs frame, stackNoFfi (compNative ac perf p bs frame).1 = true := by
  induction shape with
  | seq ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h1 : compNative ac perf _ bs frame with
    | mk pa ba =>
      cases h2 : compNative ac perf _ ba frame with
      | mk pb bb =>
        have a := iha bs frame
        have b := ihb ba frame
        simp only [h1] at a
        simp only [h2] at b
        simpa [stackNoFfi] using And.intro a b
  | ite cmp r ri ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h1 : compNative ac perf _ bs frame with
    | mk pa ba =>
      cases h2 : compNative ac perf _ ba frame with
      | mk pb bb =>
        have a := iha bs frame
        have b := ihb ba frame
        simp only [h1] at a
        simp only [h2] at b
        cases ri <;> simp [wStackLoad_noFfi,stackNoFfi,a,b]
        split <;> simp [wStackLoad_noFfi,stackNoFfi,a,b]
  | inst i => intro bs frame; simpa only [compNative] using wInst_noFfi (HolInst.ofWordLangInst i) frame
  | move priority moves => intro bs frame; simpa [compNative,wMoveNative] using wMoveAux_noFfi _ frame
  | ret register names =>
    intro bs frame
    simp only [compNative,wStackLoad_noFfi]
    unfold seqStackFreeNative
    split <;> rfl
  | opCurrHeap op dst src =>
    intro bs frame
    simp only [compNative,wStackLoad_noFfi]
    exact wRegWrite1_noFfi _ dst frame (fun _ => rfl)
  | get dst name => intro bs frame; simp only [compNative]; exact wRegWrite1_noFfi _ dst frame (fun _ => rfl)
  | set name e =>
    intro bs frame
    cases name <;> cases e <;> simp [compNative,wStackLoad_noFfi,stackNoFfi]
  | _ => intro bs frame; simp [compNative,stackNoFfi]

/-- Direct tail entries remain FFI-free under native compilation. -/
theorem regTail_compNative_noFfi {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) {p : WordLangProgHOL (BitVec width)}
    (shape : RegTailShape p) : ∀ bs frame, stackNoFfi (compNative ac perf p bs frame).1 = true := by
  induction shape with
  | branch h => exact branch_compNative_noFfi ac perf h
  | call loc reg =>
    intro bs frame
    simp only [compNative,callDestNative,stackNoFfi,Bool.true_and]
    unfold seqStackFreeNative
    split <;> rfl
  | seq ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h1 : compNative ac perf _ bs frame with
    | mk pa ba =>
      cases h2 : compNative ac perf _ ba frame with
      | mk pb bb =>
        have a := iha bs frame
        have b := ihb ba frame
        simp only [h1] at a
        simp only [h2] at b
        simpa [stackNoFfi] using And.intro a b

/-- Call-free loop sequences remain FFI-free under native compilation. -/
theorem loopSequence_compNative_noFfi {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) {p : WordLangProgHOL (BitVec width)}
    (shape : LoopSequence p) : ∀ bs frame, stackNoFfi (compNative ac perf p bs frame).1 = true := by
  induction shape with
  | branch h => exact branch_compNative_noFfi ac perf h
  | loop _ _ h =>
    intro bs frame
    simpa [compNative,stackNoFfi] using branch_compNative_noFfi ac perf h bs frame
  | seq ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h1 : compNative ac perf _ bs frame with
    | mk pa ba =>
      cases h2 : compNative ac perf _ ba frame with
      | mk pb bb =>
        have a := iha bs frame
        have b := ihb ba frame
        simp only [h1] at a
        simp only [h2] at b
        simpa [stackNoFfi] using And.intro a b

/-- Native compilation of supported functions emits only FFI-free bodies. -/
theorem compileRows_noFfi {width : Nat} [NeZero width] {β : Type}
    (ac : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (shapes : ∀ row ∈ rows, RegTailShape row.2.2 ∨ LoopSequence row.2.2) :
    ∀ bs, ∀ row ∈ (compileWordToStackNative ac perf registers rows bs).1, stackNoFfi row.2 = true := by
  induction rows with
  | nil => simp [compileWordToStackNative]
  | cons row rows ih =>
    intro bs out member
    obtain ⟨id,args,body⟩ := row
    have shape := shapes (id,args,body) (by simp)
    have bodySafe : ∀ frame, stackNoFfi (compNative ac perf body bs frame).1 = true := by
      intro frame
      rcases shape with tail | loop
      · exact regTail_compNative_noFfi ac perf tail bs frame
      · exact loopSequence_compNative_noFfi ac perf loop bs frame
    have headSafe : stackNoFfi (compileProgNative ac perf body args registers bs).1 = true := by
      simp only [compileProgNative,stackNoFfi,Bool.true_and]
      exact bodySafe _
    have tailShapes : ∀ row ∈ rows, RegTailShape row.2.2 ∨ LoopSequence row.2.2 := by
      intro row hr
      exact shapes row (by simp [hr])
    simp only [compileWordToStackNative] at member
    cases h : compileProgNative ac perf body args registers bs with
    | mk prog rest =>
      cases rest with
      | mk frame after =>
        simp only [h] at headSafe member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact headSafe
        · exact ih tailShapes after out member

/-- Native compilation of supported functions, including its two stubs,
emits an FFI-free Stack program list. -/
theorem compileNative_noFfi {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (shapes : ∀ row ∈ rows, RegTailShape row.2.2 ∨ LoopSequence row.2.2) :
    ∀ row ∈ (compileNative ac false rows).2.2.2, stackNoFfi row.2 = true := by
  intro row member
  have safe := compileRows_noFfi ac false (ac.regCount-(5+ac.avoidRegs.length)) rows shapes (.list [4],1)
  simp only [compileNative, Bool.false_eq_true, if_false,List.mem_cons] at member
  rcases member with rfl | rfl | member
  · simp [raiseStubNative,stackNoFfi]
  · simp [storeConstsStubNative,stackNoFfi]
  · exact safe row member

end SteppedFlapjack.WordToStackSteps
