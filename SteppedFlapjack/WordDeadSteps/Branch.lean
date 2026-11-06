import SteppedFlapjack.WordSsaSteps.Composition
import Flapjack.Compiler.Backend.WordAlloc.RemoveDead

/-! Dead-code removal of loop-free Word branches. -/
namespace SteppedFlapjack.WordDeadSteps
open Flapjack Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

omit [NeZero width] in
/-- Dropping skip children from a sequence keeps it loop-free. -/
theorem compactSeq_branch {a b : WordLangProgHOL (BitVec width)} (ha : Branch a) (hb : Branch b) :
    Branch (match a,b with | .skip,_ => b | _,.skip => a | _,_ => .seq a b) := by
  cases a <;> cases b <;> first | exact ha | exact hb | exact .seq ha hb

omit [NeZero width] in
/-- A conditional with two removed branches becomes skip; all other cases
remain loop-free conditionals. -/
theorem compactIte_branch (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    {a b : WordLangProgHOL (BitVec width)} (ha : Branch a) (hb : Branch b) :
    Branch (match a,b with | .skip,.skip => .skip | _,_ => .ite cmp r ri a b) := by
  cases a <;> cases b <;> first | exact .skip | exact .ite cmp r ri ha hb

/-- Dead-code elimination preserves loop-free branch shape for every liveness
set and loop context. -/
theorem removeDead_branch {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    ∀ live nlive targets, Branch (removeDead p live nlive targets).1 := by
  induction shape with
  | assign dst e => intro live nlive targets; simp only [removeDead]; exact .assign _ _
  | store e src => intro live nlive targets; simp only [removeDead]; exact .store _ _
  | skip => intro live nlive targets; simp only [removeDead]; exact .skip
  | tick => intro live nlive targets; simp only [removeDead]; exact .tick
  | ret r vs => intro live nlive targets; simp only [removeDead]; exact .ret _ _
  | «break» n => intro live nlive targets; simp only [removeDead]; exact .break _
  | «continue» n => intro live nlive targets; simp only [removeDead]; exact .continue _
  | inst i => intro live nlive targets; simp only [removeDead]; split <;> first | exact .skip | exact .inst _
  | move pri ms => intro live nlive targets; simp only [removeDead]; split <;> first | exact .skip | exact .move _ _
  | get dst n => intro live nlive targets; simp only [removeDead]; split <;> first | exact .skip | exact .get _ _
  | opCurrHeap op dst src => intro live nlive targets; simp only [removeDead]; split <;> first | exact .skip | exact .opCurrHeap _ _ _
  | set n e =>
    intro live nlive targets
    cases e <;> simp only [removeDead] <;> try {exact .set _ _}
    split <;> first | exact .skip | exact .set _ _
  | @seq a b ha hb iha ihb =>
    intro live nlive targets
    simp only [removeDead]
    rcases h : removeDead b live nlive targets with ⟨b',lb,nb⟩
    rcases k : removeDead a lb nb targets with ⟨a',la,na⟩
    have aa := iha lb nb targets
    have bb := ihb live nlive targets
    simp only [h] at bb
    simp only [k] at aa
    exact compactSeq_branch aa bb
  | @ite cmp r ri a b ha hb iha ihb =>
    intro live nlive targets
    simp only [removeDead]
    rcases h : removeDead a live nlive targets with ⟨a',la,na⟩
    rcases k : removeDead b live nlive targets with ⟨b',lb,nb⟩
    have aa := iha live nlive targets
    have bb := ihb live nlive targets
    simp only [h] at aa
    simp only [k] at bb
    exact compactIte_branch cmp r ri aa bb

/-- The dead-code pass has a static output visit bound on a branch. -/
theorem removeDead_branch_steps {p : WordLangProgHOL (BitVec width)} (shape : Branch p)
    (live : NumSet) (nlive : List WordStoreHOL) (targets : List (NumSet × NumSet))
    (s : WordSemStateFiniteExact width C F) :
    steps (removeDead p live nlive targets).1 s ≤ sizeOf (removeDead p live nlive targets).1 :=
  branch_static (removeDead_branch shape live nlive targets) s

end SteppedFlapjack.WordDeadSteps
