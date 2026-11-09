import SteppedFlapjack.WordSsaSteps.Program
import SteppedFlapjack.WordSimpSteps.Selection

/-! Instruction-selection output is supported by the SSA step proof. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordInstSteps Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Generated straight-line instruction sequences are supported SSA branches. -/
theorem straight_branch {p : WordLangProgHOL (BitVec width)} (shape : Straight p) : Branch p := by
  induction shape with
  | inst i => exact .inst i
  | move pri ms => exact .move pri ms
  | get dst n => exact .get dst n
  | setVar n src => exact .set n _
  | opCurrHeap op dst src => exact .opCurrHeap op dst src
  | skip => exact .skip
  | seq ha hb iha ihb => exact .seq iha ihb

/-- Instruction selection maps supported branches to supported SSA branches. -/
theorem select_branch (ac : AsmConfigExact width) (temp : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : Branch p) : Branch (instSelect ac temp p) := by
  induction shape with
  | assign dst e =>
    simp only [instSelect]
    exact straight_branch (selectExp_straight ac dst temp (flattenExp (pullExp e)))
  | set n e =>
    simp only [instSelect]
    exact .seq (straight_branch (selectExp_straight ac temp temp (flattenExp (pullExp e)))) (.set _ _)
  | store e src => exact straight_branch (selectStore_straight ac temp src e)
  | inst i => exact .inst _
  | move pri ms => exact .move _ _
  | get dst n => exact .get _ _
  | opCurrHeap op dst src => exact .opCurrHeap _ _ _
  | skip => exact .skip
  | tick => exact .tick
  | ret r vs => exact .ret _ _
  | «break» n => exact .break _
  | «continue» n => exact .continue _
  | seq ha hb iha ihb => simpa only [instSelect] using Branch.seq iha ihb
  | ite cmp r ri ha hb iha ihb => simpa only [instSelect] using Branch.ite cmp r ri iha ihb

/-- Instruction selection keeps sequences of branch-bodied loops in the SSA
fragment. -/
theorem select_loopSequence (ac : AsmConfigExact width) (temp : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) : LoopSequence (instSelect ac temp p) := by
  induction shape with
  | branch hp => exact .branch (select_branch ac temp hp)
  | loop names exits hp => simpa only [instSelect] using LoopSequence.loop names exits (select_branch ac temp hp)
  | seq ha hb iha ihb => simpa only [instSelect] using LoopSequence.seq iha ihb
  | nestedLoop names exits hp ih => simpa only [instSelect] using LoopSequence.nestedLoop names exits ih
  | conditional cmp r ri ha hb iha ihb => simpa only [instSelect] using LoopSequence.conditional cmp r ri iha ihb

/-- The first three actual Word-to-Word transformations have an output
visit bound in terms of the available clock and computed output syntax. -/
theorem simp_select_ssa_clock_bound (ac : AsmConfigExact width) (temp count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) :
    steps (fullSsaCcTrans count (instSelect ac temp (Flapjack.Compiler.Backend.WordSimp.compileExp p))) s ≤
      sizeOf (fullSsaCcTrans count (instSelect ac temp (Flapjack.Compiler.Backend.WordSimp.compileExp p))) * (s.clock+1) :=
  fullSsa_clock_bound count (select_loopSequence ac temp (compileExp_loopSequence shape)) s

/-- The actual Word-to-Word prefix uses the fresh temporary above WordSimp's
maximum variable; its full SSA output stays in the supported program shape. -/
theorem compilerPrefix_ssa_shape (ac : AsmConfigExact width) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    LoopSequence (fullSsaCcTrans count
      (instSelect ac (maxVarHOL (Flapjack.Compiler.Backend.WordSimp.compileExp p)+1)
        (Flapjack.Compiler.Backend.WordSimp.compileExp p))) :=
  fullSsa_loopSequence_shape count
    (select_loopSequence ac _ (compileExp_loopSequence shape))

/-- With the Word clock set to a separately established source visit bound,
the exact WordSimp, instruction-selection, and full-SSA prefix has a
syntax-computed upper bound on evaluator visits. -/
theorem compilerPrefix_ssa_steps (ac : AsmConfigExact width) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) (limit : Nat) :
    steps (fullSsaCcTrans count
      (instSelect ac (maxVarHOL (Flapjack.Compiler.Backend.WordSimp.compileExp p)+1)
        (Flapjack.Compiler.Backend.WordSimp.compileExp p))) {s with clock := limit} ≤
      sizeOf (fullSsaCcTrans count
        (instSelect ac (maxVarHOL (Flapjack.Compiler.Backend.WordSimp.compileExp p)+1)
          (Flapjack.Compiler.Backend.WordSimp.compileExp p))) * (limit+1) :=
  loopSequence_clock_bound (compilerPrefix_ssa_shape ac count shape) {s with clock := limit}

end SteppedFlapjack.WordSsaSteps
