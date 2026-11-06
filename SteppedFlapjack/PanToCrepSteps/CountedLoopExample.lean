import SteppedFlapjack.PanToCrepSteps.CountedWhile

/-! A state-changing loop checked across counted and HOL semantics. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- Starting with a word-valued local equal to one, the loop reads it, writes
zero, and rechecks the condition. Its counted execution has six steps. -/
theorem counted_while_set_zero_example {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (initial : production.locals name = some (.word 1)) (clock : source.clock ≠ 0)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let post := setVarHOLFinite (ofString name) (.val (.word 0)) source.decClockHOLFinite
    let condition : Exp (RiscV.Word 64) := .var .local name
    let body : Prog (RiscV.Word 64) := .assign .local name (.const 0)
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
      production.locals production.globals production.memory production.ffi (.while condition body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi,6) ∧
    source.evaluateHOLFiniteState (.while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0))) = (none,post) ∧
    controlSteps (.while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0))) source ≤ 6 := by
  let entry := source.decClockHOLFinite
  let pEntry := {production with clock := production.clock - 1}
  let post := setVarHOLFinite (ofString name) (.val (.word 0)) entry
  let pPost := {pEntry with locals := updatePanValueMap pEntry.locals name (.word 0)}
  have entryRel : PanSemStateRelExec pEntry entry.toExact := by
    simpa only [pEntry,entry,toExact_decClockHOLFinite] using PanSemStateRelExec.decClock rel
  have entryRanged : PanSemStateRelExecRanged pEntry := ranged.setClock _
  let entryDec : DecidablePred entry.memaddrs := by
    change DecidablePred source.memaddrs
    infer_instance
  have valid : isValidValueHOLFinite entry .local (ofString name) (.val (.word 0)) = true := by
    have parity := panValueAssignmentValid_eq_isValidValueHOLFinite pEntry entry entryRel entryRanged
      .local name nameRanged (.word (0 : BitVec 64)) (by simp [PanValueByteRanged])
    have parity' : panValueAssignmentValid pEntry.structs pEntry.locals pEntry.globals .local name (.word 0) =
        isValidValueHOLFinite entry .local (ofString name) (.val (.word 0)) := by simpa using parity
    rw [← parity']
    simp [pEntry,panValueAssignmentValid,initial,panValueShape,panShapeMatches]
  obtain ⟨bodyExec,bodyRun,postRel,postRanged,bodyBound⟩ :=
    @counted_assign_local σ pEntry entry entryDec entryRel entryRanged name nameRanged (.const 0) (by simp [ExpByteRanged])
      (.word 0) (by simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]) (by simpa using valid)
      context primitive handler functions (fuel+1)
  let postDec : DecidablePred post.memaddrs := by
    change DecidablePred source.memaddrs
    infer_instance
  have postRel' : PanSemStateRelExec pPost post.toExact := by
    simpa [pPost,post] using postRel
  have zeroCond : evalPanSemStateExp pPost (.var .local name) = some (.word 0) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,pPost,pEntry,updatePanValueMap]
  obtain ⟨restExec,restRun,restBound⟩ :=
    @counted_while_zero σ pPost post postDec postRel' postRanged (.var .local name) (by simpa [ExpByteRanged] using nameRanged)
      zeroCond context primitive handler functions (fuel+1) (.assign .local name (.const 0)) (.assign .local (ofString name) (.const 0))
  have cond : evalPanSemStateExp production (.var .local name) = some (.word 1) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,initial]
  have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+2)
      production.locals production.globals production.memory production.ffi (.assign .local name (.const 0))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
      some (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi,2) := by
    simpa [pEntry,panSemBitVec64MemoryAccess,panValueExpStepCost] using bodyExec
  have restExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+2)
      (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi
      (.while (.var .local name) (.assign .local name (.const 0)))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
      some (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi,2) := by
    simpa [pPost,pEntry,panSemBitVec64MemoryAccess,panValueExpStepCost] using restExec
  have h := counted_while_iteration production source post post rel ranged (.var .local name)
    (by simpa [ExpByteRanged] using nameRanged) 1 cond (by decide) clock context primitive handler functions (fuel+2)
    (.assign .local name (.const 0)) (.assign .local (ofString name) (.const 0))
    (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi false 2 2
    (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi) none
    (by simpa using bodyExec') (by simpa [post,entry,expToHOL] using bodyRun)
    (by simpa [entry,expToHOL,panValueExpStepCost] using bodyBound) restExec'
    (by simpa [post,entry,expToHOL] using restRun) (by simpa [post,entry,expToHOL,panValueExpStepCost] using restBound)
  simpa [post,entry,expToHOL,panValueExpStepCost] using h

end SteppedFlapjack.PanToCrepSteps
