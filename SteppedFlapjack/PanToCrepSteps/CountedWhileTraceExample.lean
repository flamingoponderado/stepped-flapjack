import SteppedFlapjack.PanToCrepSteps.CountedWhileTrace
import Flapjack.Pancake.Proofs.PanToCrep

/-! Constructing the finite trace for an actual state-changing loop. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A nonzero local set to zero yields a trace with one actual iteration. -/
theorem counted_while_set_zero_trace {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (initialWord : BitVec 64) (nonzero : initialWord ≠ 0)
    (initial : production.locals name = some (.word initialWord)) (clock : source.clock ≠ 0)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let post := setVarHOLFinite (ofString name) (.val (.word 0)) source.decClockHOLFinite
    CountedWhileTrace (.var .local name) (.assign .local name (.const 0))
      (.assign .local (ofString name) (.const 0)) context primitive handler functions (fuel+3)
      production source (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi)
      none post 6 := by
  let entry := source.decClockHOLFinite
  let pEntry := {production with clock := production.clock-1}
  let post := setVarHOLFinite (ofString name) (.val (.word 0)) entry
  let next := {production with locals := updatePanValueMap production.locals name (.word 0), clock := post.clock}
  have entryRel : PanSemStateRelExec pEntry entry.toExact := by
    simpa only [pEntry,entry,toExact_decClockHOLFinite] using PanSemStateRelExec.decClock rel
  have entryRanged : PanSemStateRelExecRanged pEntry := ranged.setClock _
  let entryDec : DecidablePred entry.memaddrs := by change DecidablePred source.memaddrs; infer_instance
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
  have sameClock : post.clock = pEntry.clock := by
    have h := postRel.2.2.2.2.2.2.2.2.1
    simpa [post] using h
  have nextEq : next = {pEntry with locals := updatePanValueMap pEntry.locals name (.word 0)} := by
    cases production
    simp_all [next,pEntry]
  have nextRel : PanSemStateRelExec next post.toExact := by rw [nextEq]; simpa [post] using postRel
  have nextRanged : PanSemStateRelExecRanged next := by rw [nextEq]; exact postRanged
  have zeroCond : evalPanSemStateExp next (.var .local name) = some (.word 0) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,next,updatePanValueMap]
  have rest := @CountedWhileTrace.zero σ (.var .local name) (.assign .local name (.const 0))
    (.assign .local (ofString name) (.const 0)) context primitive handler functions (fuel+1)
    next post nextRel nextRanged (by simpa [ExpByteRanged] using nameRanged) zeroCond
  have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+2)
      production.locals production.globals production.memory production.ffi (.assign .local name (.const 0))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
      some (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi,2) := by
    simpa [pEntry,panSemBitVec64MemoryAccess,panValueExpStepCost] using bodyExec
  have cond : evalPanSemStateExp production (.var .local name) = some (.word initialWord) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,initial]
  have traced := @CountedWhileTrace.iteration σ (.var .local name) (.assign .local name (.const 0))
    (.assign .local (ofString name) (.const 0)) context primitive handler functions (fuel+2)
    production source post post rel ranged (by simpa [ExpByteRanged] using nameRanged) initialWord cond nonzero clock
    (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi false 2 2
    (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi) none
    (by simpa using bodyExec') (by simpa [post,entry,expToHOL] using bodyRun)
    (by simpa [entry,expToHOL,panValueExpStepCost] using bodyBound) (by simpa [next,panValueExpStepCost] using rest)
  simpa [post,entry,panValueExpStepCost] using traced

end SteppedFlapjack.PanToCrepSteps
