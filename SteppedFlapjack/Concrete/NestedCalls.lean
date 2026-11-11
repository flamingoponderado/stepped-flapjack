import SteppedFlapjack.Concrete.SourceState

/-! Source witness for ordinary and tail calls at two nested call levels. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

/-- The entry function resumes after the ordinary call and returns its result. -/
def nestedCallEntry : Prog (RiscV.Word 64) :=
  .decCall "answer" .one "middle" [] (.return (.var .local "answer"))

/-- Three actual declarations: `main` calls `middle`, which tail-calls `leaf`. -/
def nestedCallDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function ⟨"main", false, true, [], nestedCallEntry, .one⟩,
   .function ⟨"middle", false, false, [], .call none "leaf" [], .one⟩,
   .function ⟨"leaf", false, false, [], .return (.const 7), .one⟩]

/-- All three declarations survive conversion to the HOL source representation. -/
theorem nestedCall_declarations_ranged :
    ∀ declaration ∈ nestedCallDeclarations, DeclByteRanged declaration := by
  simp [nestedCallDeclarations,nestedCallEntry,DeclByteRanged,FunDeclByteRanged,
    ListParamByteRanged,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged]

end SteppedFlapjack.Concrete
