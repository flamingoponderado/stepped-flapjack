import SteppedFlapjack.WordCseSteps.Correct
import Flapjack.Compiler.Backend.WordCopy.Proofs.Correct

/-! Copy propagation for sequences of branch-bodied loops. -/
namespace SteppedFlapjack.WordCopySteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordCopy SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Copy propagation maps individual instructions to loop-free code. -/
theorem copyInst_branch (i : WordLangInst (BitVec width)) (cs : CopyState) : Branch (copyPropInst i cs).1 := by
  cases i with
  | skip => exact .skip
  | const dst value => exact .inst _
  | arith a => cases a <;> simp only [copyPropInst] <;> exact .inst _
  | mem op dst addr => cases op <;> cases addr <;> simp only [copyPropInst] <;> exact .inst _

/-- Copy propagation preserves loop-free branch shape for any copy state. -/
theorem copyBranch_shape {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    ∀ cs, Branch (copyPropProg p cs).1 := by
  induction shape with
  | assign dst e => intro cs; exact .assign _ _
  | store e src => intro cs; exact .store _ _
  | skip => intro cs; exact .skip
  | tick => intro cs; exact .tick
  | ret r vs => intro cs; exact .ret _ _
  | «break» n => intro cs; exact .break _
  | «continue» n => intro cs; exact .continue _
  | opCurrHeap op dst src => intro cs; exact .opCurrHeap _ _ _
  | inst i => intro cs; exact copyInst_branch i cs
  | move pri ms =>
    intro cs
    simp only [copyPropProg]
    split
    · rcases h : copyPropMove ms cs with ⟨moves,out⟩
      exact .move _ _
    · exact .move _ _
  | get dst name =>
    intro cs
    simp only [copyPropProg]
    split
    · exact .get _ _
    · split
      · rcases h : copyPropMove [(dst,_)] cs with ⟨moves,out⟩
        exact .move _ _
      · exact .skip
  | set n e => intro cs; cases e <;> simp only [copyPropProg] <;> exact .set _ _
  | @seq a b ha hb iha ihb =>
    intro cs
    simp only [copyPropProg]
    rcases h : copyPropProg a cs with ⟨a',ca⟩
    rcases k : copyPropProg b ca with ⟨b',cb⟩
    have aa := iha cs
    have bb := ihb ca
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb
  | @ite cmp r ri a b ha hb iha ihb =>
    intro cs
    simp only [copyPropProg]
    rcases h : copyPropProg a cs with ⟨a',ca⟩
    rcases k : copyPropProg b cs with ⟨b',cb⟩
    have aa := iha cs
    have bb := ihb cs
    simp only [h] at aa
    simp only [k] at bb
    exact .ite _ _ _ aa bb

/-- Copy propagation preserves sequences of branches and branch-bodied loops. -/
theorem copyLoopSequence_shape {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    ∀ cs, LoopSequence (copyPropProg p cs).1 := by
  induction shape with
  | branch hp => intro cs; exact .branch (copyBranch_shape hp cs)
  | loop names exits hp =>
    intro cs
    simp only [copyPropProg]
    rcases h : copyPropProg _ emptyEq with ⟨body,cs'⟩
    have hb := copyBranch_shape hp emptyEq
    simp only [h] at hb
    exact .loop names exits hb
  | @seq a b ha hb iha ihb =>
    intro cs
    simp only [copyPropProg]
    rcases h : copyPropProg a cs with ⟨a',ca⟩
    rcases k : copyPropProg b ca with ⟨b',cb⟩
    have aa := iha cs
    have bb := ihb ca
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb

/-- Copy propagation preserves non-error execution and has a syntax-and-clock
bound on its actual output visits. -/
theorem copyProp_correct_with_steps {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    evaluate (copyProp p) s = (res,post) ∧
    steps (copyProp p) s ≤ sizeOf (copyProp p) * (s.clock+1) := by
  have noerror : (evaluate p s).1 ≠ some .error := by rw [run]; exact nonerror
  exact ⟨(evaluateCopyProp noerror).trans run,loopSequence_clock_bound (copyLoopSequence_shape shape emptyEq) s⟩

end SteppedFlapjack.WordCopySteps
