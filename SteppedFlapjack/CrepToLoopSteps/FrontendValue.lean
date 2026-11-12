import SteppedFlapjack.PanToCrepSteps.FrontendValue
import SteppedFlapjack.CrepToLoopSteps.FrontendScalar
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

theorem frontendValue_scalars {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (h : FrontendValue ctxt e) : ∀ value ∈ (compileExpExactHOLW ctxt e).1, CompiledScalar value := by
  induction h with
  | scalar h =>
    obtain ⟨value,compiled,shape⟩ := frontendScalar_compiled h
    rw [compiled]
    simp only [List.mem_singleton]
    intro v hv
    subst v
    exact shape
  | @tuple fields hs ih =>
    simp only [compileExpExactHOLW]
    intro value member
    simp only [List.mem_flatMap] at member
    obtain ⟨item,itemMember,valueMember⟩ := member
    have mapped : compileExpExactHOLWList ctxt fields = fields.map (compileExpExactHOLW ctxt) := frontend_compileList_map ctxt fields
    rw [mapped,List.mem_map] at itemMember
    obtain ⟨field,fieldMember,rfl⟩ := itemMember
    exact ih field fieldMember value valueMember

end SteppedFlapjack.CrepToLoopSteps
