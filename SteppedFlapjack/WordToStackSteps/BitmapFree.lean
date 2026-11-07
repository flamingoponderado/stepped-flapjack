import SteppedFlapjack.WordAllocSteps.TailEntry
import SteppedFlapjack.WordToStackSteps.LoopZeroClock
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile

/-! Word shapes that do not allocate bitmap entries during native compilation. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps

/-- A branch compiles without modifying the bitmap accumulator. -/
theorem branch_compNative_bitmap {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) {p : WordLangProgHOL (BitVec width)}
    (shape : Branch p) : ∀ bs frame, (compNative ac perf p bs frame).2 = bs := by
  induction shape with
  | seq ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h : compNative ac perf _ bs frame with
    | mk qa ba =>
      have eq : ba = bs := by simpa only [h] using iha bs frame
      subst ba
      simpa using ihb bs frame
  | ite cmp r ri ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h1 : compNative ac perf _ bs frame with
    | mk qa ba =>
      have eq : ba = bs := by simpa only [h1] using iha bs frame
      subst ba
      cases h2 : compNative ac perf _ bs frame with
      | mk qb bb =>
        have eq : bb = bs := by simpa only [h2] using ihb bs frame
        subst bb
        cases ri <;> simp only
        split <;> rfl
  | set name e => intro bs frame; cases name <;> cases e <;> simp [compNative]
  | _ => intro bs frame; simp [compNative]

/-- The post-allocation loop fragment preserves the bitmap accumulator. -/
theorem loopBlock_compNative_bitmap {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) {p : WordLangProgHOL (BitVec width)}
    (shape : LoopBlock p) : ∀ bs frame, (compNative ac perf p bs frame).2 = bs := by
  induction shape with
  | seq ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h : compNative ac perf _ bs frame with
    | mk qa ba =>
      have eq : ba = bs := by simpa only [h] using iha bs frame
      subst ba
      simpa using ihb bs frame
  | ite cmp r ri ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h1 : compNative ac perf _ bs frame with
    | mk qa ba =>
      have eq : ba = bs := by simpa only [h1] using iha bs frame
      subst ba
      cases h2 : compNative ac perf _ bs frame with
      | mk qb bb =>
        have eq : bb = bs := by simpa only [h2] using ihb bs frame
        subst bb
        cases ri <;> simp only
        split <;> rfl
  | loop _ _ h ih =>
    intro bs frame
    simpa only [compNative] using ih bs frame
  | set name e => intro bs frame; cases name <;> cases e <;> simp [compNative]
  | _ => intro bs frame; simp [compNative]


theorem loopSequence_compNative_bitmap {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) {p : WordLangProgHOL (BitVec width)}
    (shape : LoopSequence p) : ∀ bs frame, (compNative ac perf p bs frame).2 = bs := by
  induction shape with
  | branch h => exact branch_compNative_bitmap ac perf h
  | loop _ _ h =>
    intro bs frame
    simpa only [compNative] using branch_compNative_bitmap ac perf h bs frame
  | seq ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h : compNative ac perf _ bs frame with
    | mk qa ba =>
      have eq : ba = bs := by simpa only [h] using iha bs frame
      subst ba
      simpa using ihb bs frame

/-- Direct tail-entry programs likewise do not allocate bitmap entries. -/
theorem regTail_compNative_bitmap {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) {p : WordLangProgHOL (BitVec width)}
    (shape : RegTailShape p) : ∀ bs frame, (compNative ac perf p bs frame).2 = bs := by
  induction shape with
  | branch h => exact branch_compNative_bitmap ac perf h
  | call _ _ => intro bs frame; simp [compNative]
  | seq ha hb iha ihb =>
    intro bs frame
    simp only [compNative]
    cases h : compNative ac perf _ bs frame with
    | mk qa ba =>
      have eq : ba = bs := by simpa only [h] using iha bs frame
      subst ba
      simpa using ihb bs frame

/-- Compile a list of bitmap-free bodies without changing the accumulator. -/
theorem bitmapFree_compileRows {width : Nat} [NeZero width] {β : Type}
    (ac : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (shapes : ∀ row ∈ rows, RegTailShape row.2.2 ∨ LoopSequence row.2.2 ∨ LoopBlock row.2.2) :
    ∀ bs, (compileWordToStackNative ac perf registers rows bs).2.2 = bs := by
  induction rows with
  | nil => intro bs; rfl
  | cons row rows ih =>
    intro bs
    obtain ⟨id,args,body⟩ := row
    have shape := shapes (id,args,body) (by simp)
    have bodyEq : ∀ frame, (compNative ac perf body bs frame).2 = bs := by
      intro frame
      rcases shape with tail | loop | block
      · exact regTail_compNative_bitmap ac perf tail bs frame
      · exact loopSequence_compNative_bitmap ac perf loop bs frame
      · exact loopBlock_compNative_bitmap ac perf block bs frame
    have one : (compileProgNative ac perf body args registers bs).2.2 = bs := by
      simp only [compileProgNative]
      exact bodyEq _
    have tailShapes : ∀ row ∈ rows, RegTailShape row.2.2 ∨ LoopSequence row.2.2 ∨ LoopBlock row.2.2 := by
      intro row hr
      exact shapes row (by simp [hr])
    simp only [compileWordToStackNative]
    cases h : compileProgNative ac perf body args registers bs with
    | mk prog rest =>
      cases rest with
      | mk frame after =>
        have eq : after = bs := by simpa only [h] using one
        subst after
        simpa using ih tailShapes bs

/-- If each Word body is a supported loop sequence or direct tail entry,
the native compiler emits exactly its initial bitmap. -/
theorem bitmapFree_compileNative {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (shapes : ∀ row ∈ rows, RegTailShape row.2.2 ∨ LoopSequence row.2.2 ∨ LoopBlock row.2.2) :
    (compileNative ac false rows).1 = [4] := by
  let bs : AppList (BitVec width) × Nat := (.list [4],1)
  have eq := bitmapFree_compileRows ac false (ac.regCount - (5+ac.avoidRegs.length)) rows shapes bs
  simpa [compileNative,bs,appListAppend,appendAux] using congrArg (fun x => appListAppend x.1) eq

end SteppedFlapjack.WordToStackSteps
