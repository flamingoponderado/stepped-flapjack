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

/-- The executable function environment projected from the source declarations. -/
def nestedCallFunctions : List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  (functionEntries nestedCallDeclarations).map fun (name, params, body, _) =>
    (name, params.map Prod.fst, body)

/-- All three declarations survive conversion to the HOL source representation. -/
theorem nestedCall_declarations_ranged :
    ∀ declaration ∈ nestedCallDeclarations, DeclByteRanged declaration := by
  simp [nestedCallDeclarations,nestedCallEntry,DeclByteRanged,FunDeclByteRanged,
    ListParamByteRanged,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged]

set_option maxHeartbeats 3000000 in
/-- The two nested calls return seven in six counted source steps. -/
theorem nestedCall_source_run (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler [] nestedCallFunctions
      heapBase heapTop panSemBitVec64BytesInWord 8 (fun _ => none)
      (fun _ => none) (fun a => some (.word (initialWord a))) (sourceFfiState sourceFfi)
      nestedCallEntry (memoryAccess := some (panSemBitVec64MemoryAccess sourceProduction)) =
    some (.returned (fun _ => none) (fun _ => none)
      (fun a => some (.word (initialWord a))) (sourceFfiState sourceFfi) [.word 7], 6) := by
  simp [nestedCallEntry,nestedCallFunctions,nestedCallDeclarations,functionEntries,evalPanValueFfiProgSteps,evalPanValueFfiCallSteps,
    panValueCallArguments,evalPanValueExpsCounted,evalPanValueExps,evalPanValueExp.evalPanValueExps,panValueExpsStepCost,panValueExpStepCost.panValueExpsStepCost,panValueCallTarget,lookupPanFunction,
    panValueParametersValid,bindPanValueParameters,panValueReturnValid,panValueReturnResult,
    evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,
    panShapeMatches,panValueShape,updatePanValueMap,restorePanValueFfiLocal]
  funext name
  simp [restorePanValueLocal]

end SteppedFlapjack.Concrete
