import Flapjack.Compiler.Backend.RegAlloc.Executable

/-! The checked allocator input guard implies successful graph coloring. -/
namespace SteppedFlapjack.RegAllocSteps
open Flapjack Flapjack.RegAlloc Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc
open Flapjack.Translator.Monadic.MonadBase

/-- On every input accepted by the executable input guard, the original
and executable graph allocators return a coloring. The coloring is produced
by the proved allocator, rather than supplied as an assumption. -/
theorem executable_success_of_guard (algorithm : Algorithm) (costs : Option (Spt Nat))
    (limit : Nat) (moves : List (Nat × (Nat × Nat))) (tree : ClashTree)
    (forced : List (Nat × Nat)) (stackOnly : NumSet)
    (guard : nativeRegAllocInputGuard costs tree forced stackOnly = true) :
    ∃ coloring, regAllocExecutable algorithm costs limit moves tree forced stackOnly = .success coloring := by
  have bounds := (nativeRegAllocInputGuard_iff costs tree forced stackOnly).mp guard |>.2.2.2
  obtain ⟨colors,_,run⟩ := regAlloc_production algorithm (costs.map sptToAList) limit moves
    (nativeClashTreeToProduction tree) forced ((sptToAList stackOnly).map Prod.fst) bounds
  refine ⟨sptFromAList colors,?_⟩
  unfold regAllocExecutable
  simp only [guard,if_true,Option.map_map,Function.comp_def] at *
  rw [run]

end SteppedFlapjack.RegAllocSteps
