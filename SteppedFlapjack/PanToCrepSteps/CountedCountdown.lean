import SteppedFlapjack.PanToCrepSteps.CountedWhileTrace
import SteppedFlapjack.PanToCrepSteps.CountedDeclList
import Flapjack.Pancake.Proofs.PanToCrep

/-! Counted/HOL correspondence for an arbitrary finite countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A loop body decrementing a word-valued local. -/
def countdownBody (name : VarName) : Prog (RiscV.Word 64) :=
  .assign .local name (.op .sub [.var .local name,.const 1])

/-- The corresponding HOL loop body. -/
def countdownBodyHOL (name : VarName) : ProgHOL 64 :=
  .assign .local (ofString name) (.op .sub [.var .local (ofString name),.const 1])

/-- Every finite countdown within the word range produces a trace, without a
separately assumed loop or body correspondence. -/
theorem counted_countdown_trace {σ : Type} (count : Nat)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    ∀ (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs],
      PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production →
      ∀ (name : VarName), NameRanged name →
      production.locals name = some (.word (BitVec.ofNat 64 count)) →
      count < 2^64 → count ≤ source.clock → ∀ (fuel : Nat),
      ∃ result final,
        CountedWhileTrace (.var .local name) (countdownBody name) (countdownBodyHOL name)
          context primitive handler functions (fuel+count+1) production source result none final (6*count+2) := by
  induction count with
  | zero =>
    intro production source dec rel ranged name nameRanged initial wordRange clock fuel
    have cond : evalPanSemStateExp production (.var .local name) = some (.word 0) := by
      simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,initial]
    have trace := @CountedWhileTrace.zero σ (.var .local name) (countdownBody name) (countdownBodyHOL name)
      context primitive handler functions fuel production source rel ranged
      (by simpa [ExpByteRanged] using nameRanged) cond
    exact ⟨_,_,by simpa [panValueExpStepCost] using trace⟩
  | succ count ih =>
    intro production source dec rel ranged name nameRanged initial wordRange clock fuel
    let entry := source.decClockHOLFinite
    let pEntry := {production with clock := production.clock-1}
    let post := setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 count))) entry
    let next := {production with locals := updatePanValueMap production.locals name (.word (BitVec.ofNat 64 count)), clock := post.clock}
    have nonzero : BitVec.ofNat 64 (count+1) ≠ 0 := by
      intro zero
      have h := congrArg BitVec.toNat zero
      change (count+1) % 2^64 = 0 at h
      rw [Nat.mod_eq_of_lt wordRange] at h
      omega
    have sub : BitVec.ofNat 64 (count+1) - 1 = BitVec.ofNat 64 count := by
      simpa using (BitVec.ofNat_sub_ofNat_of_le (w := 64) (count+1) 1 (by decide) (by omega))
    have entryRel : PanSemStateRelExec pEntry entry.toExact := by
      simpa only [pEntry,entry,toExact_decClockHOLFinite] using PanSemStateRelExec.decClock rel
    have entryRanged : PanSemStateRelExecRanged pEntry := ranged.setClock _
    let entryDec : DecidablePred entry.memaddrs := by change DecidablePred source.memaddrs; infer_instance
    have valid : isValidValueHOLFinite entry .local (ofString name) (.val (.word (BitVec.ofNat 64 count))) = true := by
      have parity := panValueAssignmentValid_eq_isValidValueHOLFinite pEntry entry entryRel entryRanged
        .local name nameRanged (.word (BitVec.ofNat 64 count)) (by simp [PanValueByteRanged])
      have parity' : panValueAssignmentValid pEntry.structs pEntry.locals pEntry.globals .local name (.word (BitVec.ofNat 64 count)) =
          isValidValueHOLFinite entry .local (ofString name) (.val (.word (BitVec.ofNat 64 count))) := by simpa using parity
      rw [← parity']
      simp [pEntry,panValueAssignmentValid,initial,panValueShape,panShapeMatches]
    have exprRun : evalPanSemStateExp pEntry (.op .sub [.var .local name,.const 1]) = some (.word (BitVec.ofNat 64 count)) := by
      simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,evalPanValueExp.evalPanValueExps,
        panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,panSemWordModel,
        RiscV.panRiscVMemoryModel,RiscV.panRiscVWordOp,wordOpHOL,wordOp,panValueWordProjection,pEntry,initial]
      exact sub
    obtain ⟨bodyExec,bodyRun,postRel,postRanged,bodyBound⟩ :=
      @counted_assign_local σ pEntry entry entryDec entryRel entryRanged name nameRanged
        (.op .sub [.var .local name,.const 1]) (by simpa [ExpByteRanged,ListExpByteRanged] using nameRanged)
        (.word (BitVec.ofNat 64 count)) exprRun (by simpa using valid) context primitive handler functions (fuel+count)
    have sameClock : post.clock = pEntry.clock := by
      have h := postRel.2.2.2.2.2.2.2.2.1
      simpa [post] using h
    have nextEq : next = {pEntry with locals := updatePanValueMap pEntry.locals name (.word (BitVec.ofNat 64 count))} := by
      cases production
      simp_all [next,pEntry]
    have nextRel : PanSemStateRelExec next post.toExact := by rw [nextEq]; simpa [post] using postRel
    have nextRanged : PanSemStateRelExecRanged next := by rw [nextEq]; exact postRanged
    let postDec : DecidablePred post.memaddrs := by change DecidablePred source.memaddrs; infer_instance
    have nextInitial : next.locals name = some (.word (BitVec.ofNat 64 count)) := by simp [next,updatePanValueMap]
    have nextClock : count ≤ post.clock := by simp [post,entry,setVarHOLFinite,decClockHOLFinite]; omega
    obtain ⟨result,final,rest⟩ := @ih next post postDec nextRel nextRanged name nameRanged nextInitial (by omega) nextClock fuel
    have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+1)
        production.locals production.globals production.memory production.ffi (countdownBody name)
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal (updatePanValueMap production.locals name (.word (BitVec.ofNat 64 count)))
          production.globals production.memory production.ffi,4) := by
      simpa [pEntry,countdownBody,panSemBitVec64MemoryAccess,panValueExpStepCost,panValueExpStepCost.panValueExpsStepCost] using bodyExec
    have cond : evalPanSemStateExp production (.var .local name) = some (.word (BitVec.ofNat 64 (count+1))) := by
      simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,initial]
    have traced := @CountedWhileTrace.iteration σ (.var .local name) (countdownBody name) (countdownBodyHOL name)
      context primitive handler functions (fuel+count+1) production source post final rel ranged
      (by simpa [ExpByteRanged] using nameRanged) (BitVec.ofNat 64 (count+1)) cond nonzero (by omega)
      (updatePanValueMap production.locals name (.word (BitVec.ofNat 64 count))) production.globals production.memory production.ffi
      false 4 (6*count+2) result none (by simpa using bodyExec')
      (by simpa [post,entry,countdownBodyHOL,expToHOL] using bodyRun)
      (by simpa [entry,countdownBodyHOL,expToHOL,panValueExpStepCost,panValueExpStepCost.panValueExpsStepCost] using bodyBound)
      (by simpa [next] using rest)
    have costEq : panValueExpStepCost (.var .local name : Exp (RiscV.Word 64)) + 4 + (6*count+2) + 1 =
        6*(count+1)+2 := by simp [panValueExpStepCost]; omega
    have fuelEq : fuel+count+1+1 = fuel+(count+1)+1 := by omega
    rw [costEq,fuelEq] at traced
    exact ⟨result,final,traced⟩

/-- The countdown's actual source execution costs `6 * count + 2` steps and
its HOL control visits are bounded by that count. -/
theorem counted_countdown {σ : Type} (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (initial : production.locals name = some (.word (BitVec.ofNat 64 count)))
    (wordRange : count < 2^64) (clock : count ≤ source.clock)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+1)
        production.locals production.globals production.memory production.ffi
        (.while (.var .local name) (countdownBody name))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+2) ∧
      source.evaluateHOLFiniteState (.while (.var .local (ofString name)) (countdownBodyHOL name)) = (none,final) ∧
      controlSteps (.while (.var .local (ofString name)) (countdownBodyHOL name)) source ≤ 6*count+2 := by
  obtain ⟨result,final,trace⟩ := counted_countdown_trace count context primitive handler functions
    production source rel ranged name nameRanged initial wordRange clock fuel
  refine ⟨result,final,?_⟩
  simpa [expToHOL] using counted_while_trace (.var .local name) (countdownBody name) (countdownBodyHOL name)
    context primitive handler functions trace

/-- A finite list of scalar declarations around the countdown has the actual
source cost `2 * declarations.length + 6 * count + 2`. -/
theorem counted_declList_countdown {σ : Type} (declarations : List (VarName × BitVec 64)) (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (names : ∀ item ∈ declarations, NameRanged item.1) (name : VarName) (nameRanged : NameRanged name)
    (initial : (enterCountedDeclList declarations production).locals name = some (.word (BitVec.ofNat 64 count)))
    (wordRange : count < 2^64) (clock : count ≤ (enterCountedDeclListHOL declarations source).clock)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+1+declarations.length)
        production.locals production.globals production.memory production.ffi
        (wrapCountedDeclList declarations (.while (.var .local name) (countdownBody name)))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,2*declarations.length+(6*count+2)) ∧
      source.evaluateHOLFiniteState
        (wrapCountedDeclListHOL declarations (.while (.var .local (ofString name)) (countdownBodyHOL name))) = (none,final) ∧
      controlSteps (wrapCountedDeclListHOL declarations (.while (.var .local (ofString name)) (countdownBodyHOL name))) source ≤
        2*declarations.length+(6*count+2) := by
  let entry := enterCountedDeclList declarations production
  let exactEntry := enterCountedDeclListHOL declarations source
  let entryDec : DecidablePred exactEntry.memaddrs := by
    rw [enterCountedDeclListHOL_memaddrs]
    infer_instance
  have ⟨entryRel,entryRanged⟩ := enterCountedDeclList_rel declarations production source rel ranged names
  obtain ⟨result,final,bodyExec,bodyRun,bodyBound⟩ := @counted_countdown σ count entry exactEntry entryDec
    entryRel entryRanged name nameRanged initial wordRange clock context primitive handler functions fuel
  exact counted_declList_wrap declarations (.while (.var .local name) (countdownBody name))
    (.while (.var .local (ofString name)) (countdownBodyHOL name)) context primitive handler functions
    production source rel ranged names (fuel+count+1) (6*count+2) result none final bodyExec bodyRun bodyBound

end SteppedFlapjack.PanToCrepSteps
