import SteppedFlapjack.PanToCrepSteps.CountedIte

/-! Counted scalar declarations and source-local restoration. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A word-valued declaration enters its body with the new local binding,
counts the initializer and declaration node, then restores the previous local
in both semantics. -/
theorem counted_decl_word {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source bodyFinal : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (initializer : Exp (RiscV.Word 64)) (initializerRanged : ExpByteRanged initializer)
    (word : BitVec 64) (initializerRun : evalPanSemStateExp production initializer = some (.word word))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (body : Prog (RiscV.Word 64)) (bodyHOL : ProgHOL 64)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ) (holResult : Option (PanSemResultExact 64)) (bodyCost : Nat)
    (bodyExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      (updatePanValueMap production.locals name (.word word)) production.globals production.memory production.ffi body
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,bodyCost))
    (bodyRun : (setVarHOLFinite (ofString name) (.val (.word word)) source).evaluateHOLFiniteState bodyHOL = (holResult,bodyFinal))
    (bodyBound : controlSteps bodyHOL (setVarHOLFinite (ofString name) (.val (.word word)) source) ≤ bodyCost) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.dec name .one initializer body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
      some (restorePanValueFfiLocal name (production.locals name) result,panValueExpStepCost initializer+bodyCost+1) ∧
    source.evaluateHOLFiniteState (.dec (ofString name) .one (expToHOL initializer) bodyHOL) =
      (holResult,{bodyFinal with locals := HolFiniteMapExact.resVarEq bodyFinal.locals (ofString name,source.locals.lookup (ofString name))}) ∧
    controlSteps (.dec (ofString name) .one (expToHOL initializer) bodyHOL) source ≤
      panValueExpStepCost initializer+bodyCost+1 := by
  have previous : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord initializer
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (.word word) := by
    simpa only [evalPanSemStateExp_64_eq_previous] using initializerRun
  have counted : evalPanValueExpCounted production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord initializer
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.word word,panValueExpStepCost initializer) := by simp [evalPanValueExpCounted,previous]
  obtain ⟨_,exactEval⟩ := counted_condition_word production source rel ranged initializer initializerRanged word initializerRun
  have valid : shapeEqHOL .one (shapeOfHOLExact (.val (.word word))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
  constructor
  · rw [evalPanValueFfiProgSteps]
    simp [panValueDecAccepted,counted,panValueShape,panShapeMatches,bodyExec]
  · constructor
    · rw [evaluateHOLFiniteState_dec_total]
      simp only [exactEval,valid,if_true,bodyRun]
    · rw [controlSteps_dec _ _ _ _ _ _ exactEval valid]
      omega

end SteppedFlapjack.PanToCrepSteps
