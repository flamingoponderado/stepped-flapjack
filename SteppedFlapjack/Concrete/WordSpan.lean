import SteppedFlapjack.Concrete.WordStarter
import SteppedFlapjack.Concrete.WordTables
import SteppedFlapjack.LoopToWordSteps.WholeWordSpan
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
variable {C F : Type}
/-- A uniform bound for all looked-up functions bounds the table maximum. -/
private theorem wordCodeWeight_le (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (limit : Nat)
    (positive : 1 ≤ limit)
    (entries : ∀ loc arity body, sptLookup loc code = some (arity,body) → wordControlWeight body ≤ limit) :
    wordCodeWeight code ≤ limit := by
  unfold wordCodeWeight
  have aux : ∀ rows : List (Nat × (Nat × WordLangProgHOL (BitVec 64))),
      (∀ row ∈ rows, wordControlWeight row.2.2 ≤ limit) →
      rows.foldr (fun row weight => max (wordControlWeight row.2.2) weight) 1 ≤ limit := by
    intro rows bound
    induction rows with
    | nil => exact positive
    | cons row rest ih =>
      simp only [List.foldr_cons,Nat.max_le]
      exact ⟨bound row (by simp),ih (fun r hr => bound r (by simp [hr]))⟩
  apply aux
  intro row member
  exact entries row.1 row.2.1 row.2.2 ((sptToAList_mem_iff_lookup code row.1 row.2).mp member)

private theorem wordWeight_positive (p : WordLangProgHOL (BitVec 64)) : 1 ≤ wordControlWeight p := by
  cases p <;> (try simp only [wordControlWeight]) <;> try omega
  case call ret dest args handler =>
    cases ret <;> cases handler <;> simp [wordControlWeight]
    all_goals omega

private theorem sequence_to_simple {p : HolLoopProg 64} (shape : LoopSequenceSource p) :
    SimpleLoopSequenceSource p := by
  induction shape with
  | branch h => exact .branch h
  | loop live exits h => exact .loop live exits (.branch h)
  | seq _ _ a b => exact .seq a b
  | nestedLoop live exits _ ih => exact .loop live exits ih
  | conditional cmp r ri live _ _ a b => exact .conditional cmp r ri live a b

end SteppedFlapjack.Concrete
