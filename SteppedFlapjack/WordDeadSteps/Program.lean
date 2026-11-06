import SteppedFlapjack.WordDeadSteps.Branch

/-! Dead-code removal on SSA loop sequences. -/
namespace SteppedFlapjack.WordDeadSteps
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

omit [NeZero width] in
/-- Removing skip children preserves the sequence-of-loops fragment. -/
theorem compactSeq_loopSequence {a b : WordLangProgHOL (BitVec width)} (ha : LoopSequence a) (hb : LoopSequence b) :
    LoopSequence (match a,b with | .skip,_ => b | _,.skip => a | _,_ => .seq a b) := by
  cases a <;> cases b <;> first | exact ha | exact hb | exact .seq ha hb

/-- Dead-code removal preserves the non-nested loop-sequence fragment. -/
theorem removeDead_loopSequence {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    ∀ live nlive targets, LoopSequence (removeDead p live nlive targets).1 := by
  induction shape with
  | branch hp => intro live nlive targets; exact .branch (removeDead_branch hp live nlive targets)
  | loop names exits hb =>
    intro live nlive targets
    simp only [removeDead]
    exact .loop names exits (removeDead_branch hb names [] ((names,exits)::targets))
  | @seq a b ha hb iha ihb =>
    intro live nlive targets
    simp only [removeDead]
    rcases h : removeDead b live nlive targets with ⟨b',lb,nb⟩
    rcases k : removeDead a lb nb targets with ⟨a',la,na⟩
    have aa := iha lb nb targets
    have bb := ihb live nlive targets
    simp only [h] at bb
    simp only [k] at aa
    exact compactSeq_loopSequence aa bb

/-- The actual dead-code pass has a syntax-and-clock visit bound. -/
theorem removeDeadProg_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) :
    steps (removeDeadProg p) s ≤ sizeOf (removeDeadProg p) * (s.clock+1) :=
  loopSequence_clock_bound (removeDead_loopSequence shape .ln [] []) s

/-- The exact compiler prefix through its first dead-code elimination pass
has a syntax-and-clock visit bound. -/
theorem compilerPrefix_removeDead_steps (ac : AsmConfigExact width) (count : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) (limit : Nat) :
    steps (removeDeadProg (fullSsaCcTrans count
      (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))) {s with clock := limit} ≤
      sizeOf (removeDeadProg (fullSsaCcTrans count
        (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p)))) * (limit+1) :=
  removeDeadProg_clock_bound (compilerPrefix_ssa_shape ac count shape) {s with clock := limit}

end SteppedFlapjack.WordDeadSteps
