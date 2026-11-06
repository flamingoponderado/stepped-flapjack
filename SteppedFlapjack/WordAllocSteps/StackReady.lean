import SteppedFlapjack.WordAllocSteps.Prefix
import SteppedFlapjack.WordToStackSteps.CallSequence
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileConventions.Output

/-! Structural and convention facts needed by the Word-to-Stack simulation. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.WordAlloc Flapjack.WordConvs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordToStackSteps
variable {width : Nat} [NeZero width]

theorem flat_branch_block {p : WordLangProgHOL (BitVec width)} (h : Branch p)
    (flat : flatExpConventions p = true) : LoopBlock p := by
  induction h with
  | assign _ _ | store _ _ => simp [flatExpConventions] at flat
  | inst i => exact .inst i
  | move pri ms => exact .move pri ms
  | get dst name => exact .get dst name
  | opCurrHeap op dst src => exact .opCurrHeap op dst src
  | set name exp => exact .set name exp
  | skip => exact .skip
  | tick => exact .tick
  | ret r vs => exact .ret r vs
  | «break» n => exact .break n
  | «continue» n => exact .continue n
  | seq _ _ ih1 ih2 =>
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact .seq (ih1 flat.1) (ih2 flat.2)
  | ite cmp r ri _ _ ih1 ih2 =>
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact .ite cmp r ri (ih1 flat.1) (ih2 flat.2)

theorem flat_loopSequence_block {p : WordLangProgHOL (BitVec width)} (h : LoopSequence p)
    (flat : flatExpConventions p = true) : LoopBlock p := by
  induction h with
  | branch h => exact flat_branch_block h flat
  | loop names exits h => exact .loop names exits (flat_branch_block h flat)
  | seq _ _ ih1 ih2 =>
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact .seq (ih1 flat.1) (ih2 flat.2)

theorem branch_noInstall {p : WordLangProgHOL (BitVec width)} (h : Branch p) :
    noInstallSubprogsHOL p = true := by
  induction h <;> simp_all [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]

theorem loopSequence_noInstall {p : WordLangProgHOL (BitVec width)} (h : LoopSequence p) :
    noInstallSubprogsHOL p = true := by
  induction h with
  | branch h => exact branch_noInstall h
  | loop names exits h => simpa [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using branch_noInstall h
  | seq _ _ ih1 ih2 =>
    simp only [noInstallSubprogsHOL] at ih1 ih2 ⊢
    simp only [notCreatedSubprogsWithMemOp,ih1,ih2,Bool.and_self]

/-- The allocator output satisfies the stack compiler’s flat-expression and
post-allocation conventions, without assumptions on the source. -/
theorem fullCompileSingle_stackConventions (ac : AsmConfigExact width) (flag : Bool)
    (count name alg regCount : Nat) (p : WordLangProgHOL (BitVec width)) (col : Option (Spt Nat)) :
    let out := (fullCompileSingle flag regCount alg ac ((name,count,p),col)).2.2
    flatExpConventions out = true ∧ postAllocConventionsHOL regCount out = true := by
  simp only [fullCompileSingle, compileSingle]
  constructor
  · apply (removeMustTerminateConventions (fun _ => true) _ ac regCount).1
    apply wordAlloc_flatExpConventions
    apply (removeDeadProgConventions (fun _ => true) _ ac).1
    apply flatExpConventions_removeUnreach
    apply threeToTwoRegProg_flatExpConventions
    apply flat_exp_conventions_copy_prop
    apply flat_exp_conventions_word_common_subexp_elim
    apply (removeDeadProgConventions (fun _ => true) _ ac).1
    apply Flapjack.WordAlloc.fullSsaCcTrans_flatExpConventions
    exact instSelect_flatExpConventions _ _ _
  · apply (removeMustTerminateConventions (fun _ => true) _ ac regCount).2.2.1
    apply Flapjack.WordAlloc.prePostConventions_wordAlloc
    apply (removeDeadProgConventions (fun _ => true) _ ac).2.2.1
    apply preAllocConventions_removeUnreach
    apply threeToTwoRegProg_preAllocConventions
    apply pre_alloc_conventions_copy_prop
    apply Flapjack.Compiler.Backend.WordCse.pre_alloc_conventions_word_common_subexp_elim
    apply (removeDeadProgConventions (fun _ => true) _ ac).2.2.1
    exact Flapjack.WordAlloc.fullSsaCcTrans_preAllocConventions _ _

/-- The real fully compiled output falls within the proved Word-to-Stack
simulation fragment and satisfies its post-allocation convention. -/
theorem fullCompileSingle_stackReady (ac : AsmConfigExact width) (flag : Bool)
    (count name alg regCount : Nat) {p : WordLangProgHOL (BitVec width)}
    (col : Option (Spt Nat)) (shape : LoopSequence p) :
    let out := (fullCompileSingle flag regCount alg ac ((name,count,p),col)).2.2
    LoopBlock out ∧ noInstallSubprogsHOL out = true ∧
      flatExpConventions out = true ∧ postAllocConventionsHOL regCount out = true := by
  have outputShape : LoopSequence (fullCompileSingle flag regCount alg ac ((name,count,p),col)).2.2 := by
    rw [fullCompileSingle_eq_alloc ac flag count name alg regCount col shape]
    exact wordAlloc_loopSequence name ac alg regCount col (preAlloc_shape ac flag count shape)
  have conventions := fullCompileSingle_stackConventions ac flag count name alg regCount p col
  exact ⟨flat_loopSequence_block outputShape conventions.1,loopSequence_noInstall outputShape,conventions.1,conventions.2⟩

end SteppedFlapjack.WordAllocSteps
