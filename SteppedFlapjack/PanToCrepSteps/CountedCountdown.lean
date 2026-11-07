import SteppedFlapjack.PanToCrepSteps.CountedWhileTrace
import SteppedFlapjack.PanToCrepSteps.CountedDeclList
import SteppedFlapjack.PanToCrepSteps.DeclLoopShape
import SteppedFlapjack.PanToCrepSteps.GlobalDecl
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations
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
      ∃ finalLocals final,
        CountedWhileTrace (.var .local name) (countdownBody name) (countdownBodyHOL name)
          context primitive handler functions (fuel+count+1) production source
          (.normal finalLocals production.globals production.memory production.ffi) none final (6*count+2) ∧
        PanSemStateRelExec {production with locals := finalLocals, clock := final.clock} final.toExact ∧
        PanSemStateRelExecRanged {production with locals := finalLocals, clock := final.clock} := by
  induction count with
  | zero =>
    intro production source dec rel ranged name nameRanged initial wordRange clock fuel
    have cond : evalPanSemStateExp production (.var .local name) = some (.word 0) := by
      simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,initial]
    have trace := @CountedWhileTrace.zero σ (.var .local name) (countdownBody name) (countdownBodyHOL name)
      context primitive handler functions fuel production source rel ranged
      (by simpa [ExpByteRanged] using nameRanged) cond
    have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
    refine ⟨production.locals,source,?_,?_,?_⟩
    · simpa [panValueExpStepCost] using trace
    · simpa [clockEq] using rel
    · simpa [clockEq] using ranged
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
    obtain ⟨finalLocals,final,rest,finalRel,finalRanged⟩ := @ih next post postDec nextRel nextRanged name nameRanged nextInitial (by omega) nextClock fuel
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
      false 4 (6*count+2) (.normal finalLocals production.globals production.memory production.ffi) none (by simpa using bodyExec')
      (by simpa [post,entry,countdownBodyHOL,expToHOL] using bodyRun)
      (by simpa [entry,countdownBodyHOL,expToHOL,panValueExpStepCost,panValueExpStepCost.panValueExpsStepCost] using bodyBound)
      (by simpa [next] using rest)
    have costEq : panValueExpStepCost (.var .local name : Exp (RiscV.Word 64)) + 4 + (6*count+2) + 1 =
        6*(count+1)+2 := by simp [panValueExpStepCost]; omega
    have fuelEq : fuel+count+1+1 = fuel+(count+1)+1 := by omega
    rw [costEq,fuelEq] at traced
    refine ⟨finalLocals,final,traced,?_,?_⟩
    · simpa [next] using finalRel
    · simpa [next] using finalRanged

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
    ∃ finalLocals final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+1)
        production.locals production.globals production.memory production.ffi
        (.while (.var .local name) (countdownBody name))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.normal finalLocals production.globals production.memory production.ffi,6*count+2) ∧
      source.evaluateHOLFiniteState (.while (.var .local (ofString name)) (countdownBodyHOL name)) = (none,final) ∧
      controlSteps (.while (.var .local (ofString name)) (countdownBodyHOL name)) source ≤ 6*count+2 ∧
      PanSemStateRelExec {production with locals := finalLocals, clock := final.clock} final.toExact ∧
      PanSemStateRelExecRanged {production with locals := finalLocals, clock := final.clock} := by
  obtain ⟨finalLocals,final,trace,finalRel,finalRanged⟩ := counted_countdown_trace count context primitive handler functions
    production source rel ranged name nameRanged initial wordRange clock fuel
  obtain ⟨exec,run,bound⟩ := counted_while_trace (.var .local name) (countdownBody name) (countdownBodyHOL name)
    context primitive handler functions trace
  exact ⟨finalLocals,final,exec,by simpa [expToHOL] using run,by simpa [expToHOL] using bound,finalRel,finalRanged⟩

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
  obtain ⟨finalLocals,final,bodyExec,bodyRun,bodyBound,_,_⟩ := @counted_countdown σ count entry exactEntry entryDec
    entryRel entryRanged name nameRanged initial wordRange clock context primitive handler functions fuel
  exact counted_declList_wrap declarations (.while (.var .local name) (countdownBody name))
    (.while (.var .local (ofString name)) (countdownBodyHOL name)) context primitive handler functions
    production source rel ranged names (fuel+count+1) (6*count+2)
    (.normal finalLocals entry.globals entry.memory entry.ffi) none final bodyExec bodyRun bodyBound

/-- The simplified countdown loop followed by a constant return has the
exact cost of the source form emitted by the simplifier. -/
theorem counted_countdown_seq_return {σ : Type} (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (initial : production.locals name = some (.word (BitVec.ofNat 64 count)))
    (wordRange : count < 2^64) (clock : count ≤ source.clock) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+2)
        production.locals production.globals production.memory production.ffi
        (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+5) ∧
      source.evaluateHOLFiniteState
        (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))) =
          (some (.returned (.val (.word returned))),final) ∧
      controlSteps (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))
        source ≤ 6*count+5 ∧
      result = .returned (fun _ => none) production.globals production.memory production.ffi [.word returned] := by
  classical
  obtain ⟨finalLocals,middle,loopExec,loopRun,loopBound,middleRel,middleRanged⟩ :=
    counted_countdown count production source rel ranged name nameRanged initial wordRange clock context primitive handler functions fuel
  let middleProduction := {production with locals := finalLocals, clock := middle.clock}
  obtain ⟨returnExec,returnRun,_,returnBound⟩ := counted_return_word_related middleProduction middle middleRel middleRanged
    (.const returned) (by simp [ExpByteRanged]) returned (by simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp])
    context primitive handler functions (fuel+count)
  have returnExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+1)
      finalLocals production.globals production.memory production.ffi (.return (.const returned))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned (fun _ => none) production.globals production.memory production.ffi [.word returned],2) := by
    simpa [middleProduction,panSemBitVec64MemoryAccess,panValueExpStepCost] using returnExec
  obtain ⟨exec,run,bound⟩ := counted_seq_normal context primitive handler production.structs functions
    production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+1)
    production.locals production.globals production.memory production.ffi
    finalLocals production.globals production.memory production.ffi
    (.while (.var .local name) (countdownBody name)) (.return (.const returned))
    (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))
    (some (panSemBitVec64MemoryAccess production)) none none
    (.returned (fun _ => none) production.globals production.memory production.ffi [.word returned])
    (6*count+2) 2 source middle (emptyLocalsHOLFinite middle) (some (.returned (.val (.word returned))))
    loopExec returnExec' loopRun (by simpa [expToHOL] using returnRun) loopBound (by simpa [expToHOL,panValueExpStepCost] using returnBound)
  refine ⟨_,_,?_,run,?_,rfl⟩
  · simpa only [show 6*count+2+2+1 = 6*count+5 by omega, show fuel+count+1+1 = fuel+count+2 by omega] using exec
  · simpa only [show 6*count+2+2+1 = 6*count+5 by omega] using bound

/-- The countdown followed by a constant word return has an exact counted
cost, a matching HOL return, and a control-visit bound. -/
theorem counted_countdown_with_return {σ : Type} (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (initial : production.locals name = some (.word (BitVec.ofNat 64 count)))
    (wordRange : count < 2^64) (clock : count ≤ source.clock) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+3)
        production.locals production.globals production.memory production.ffi
        (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+7) ∧
      source.evaluateHOLFiniteState
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))) =
          (some (.returned (.val (.word returned))),final) ∧
      controlSteps (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
        source ≤ 6*count+7 ∧
      result = .returned (fun _ => none) production.globals production.memory production.ffi [.word returned] := by
  classical
  obtain ⟨result,innerFinal,innerExec,innerRun,innerBound,resultEq⟩ :=
    counted_countdown_seq_return count production source rel ranged name nameRanged initial wordRange clock returned
      context primitive handler functions fuel
  rw [resultEq] at innerExec
  have skipExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+2)
      production.locals production.globals production.memory production.ffi .skip
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal production.locals production.globals production.memory production.ffi,1) := by
    rw [evalPanValueFfiProgSteps]
  have skipBound : controlSteps (.skip : ProgHOL 64) source ≤ 1 := by rw [controlSteps.eq_def]; rfl
  obtain ⟨exec,run,bound⟩ := counted_seq_normal context primitive handler production.structs functions
    production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+2)
    production.locals production.globals production.memory production.ffi
    production.locals production.globals production.memory production.ffi .skip
    (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))
    (.skip : ProgHOL 64) (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))
    (some (panSemBitVec64MemoryAccess production)) none none
    (.returned (fun _ => none) production.globals production.memory production.ffi [.word returned])
    1 (6*count+5) source source innerFinal (some (.returned (.val (.word returned))))
    skipExec innerExec (evaluateHOLFiniteState_skip source) innerRun skipBound innerBound
  have costEq : 1+(6*count+5)+1 = 6*count+7 := by omega
  have fuelEq : fuel+count+2+1 = fuel+count+3 := by omega
  rw [costEq,fuelEq] at exec
  rw [costEq] at bound
  exact ⟨_,_,exec,run,bound,rfl⟩

/-- The simplified declared countdown produced by the first compiler pass
has exact source cost `6 * count + 7`. -/
theorem counted_decl_countdown_simplified {σ : Type} (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64) (clock : count ≤ source.clock)
    (returned : BitVec 64) (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let program : Prog (RiscV.Word 64) := .dec name .one (.const (BitVec.ofNat 64 count))
      (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))
    let holProgram : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+3)
        production.locals production.globals production.memory production.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+7) ∧
      source.evaluateHOLFiniteState holProgram = (some (.returned (.val (.word returned))),final) ∧
      controlSteps holProgram source ≤ 6*count+7 ∧
      result = .returned (restorePanValueLocal (fun _ => none) name (production.locals name))
        production.globals production.memory production.ffi [.word returned] := by
  classical
  let word := BitVec.ofNat 64 count
  let entry := setVarHOLFinite (ofString name) (.val (.word word)) source
  let productionEntry := {production with locals := updatePanValueMap production.locals name (.word word)}
  let entryDec : DecidablePred entry.memaddrs := by change DecidablePred source.memaddrs; infer_instance
  have entryRel : PanSemStateRelExec productionEntry entry.toExact := by
    simpa [productionEntry,entry] using PanSemStateRelExec.updateLocals rel name nameRanged (.word word)
  have entryRanged : PanSemStateRelExecRanged productionEntry := by
    exact PanSemStateRelExecRanged.updateLocals ranged name (.word word) (by simp [PanValueByteRanged])
  have initial : productionEntry.locals name = some (.word (BitVec.ofNat 64 count)) := by simp [productionEntry,word,updatePanValueMap]
  have entryClock : count ≤ entry.clock := by simpa [entry,setVarHOLFinite] using clock
  obtain ⟨result,final,bodyExec,bodyRun,bodyBound,resultEq⟩ := @counted_countdown_seq_return σ count productionEntry entry entryDec
    entryRel entryRanged name nameRanged initial wordRange entryClock returned context primitive handler functions fuel
  have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+2)
      (updatePanValueMap production.locals name (.word word)) production.globals production.memory production.ffi
      (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+5) := by
    simpa [productionEntry,panSemBitVec64MemoryAccess] using bodyExec
  have initRun : evalPanSemStateExp production (.const word) = some (.word word) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
  obtain ⟨exec,run,bound⟩ := counted_decl_word production source final rel ranged name (.const word)
    (by simp [ExpByteRanged]) word initRun context primitive handler functions (fuel+count+2)
    (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))
    (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))
    result (some (.returned (.val (.word returned)))) (6*count+5) bodyExec' bodyRun bodyBound
  have costEq : panValueExpStepCost (.const word : Exp (RiscV.Word 64)) + (6*count+5) + 1 = 6*count+7 := by
    simp [panValueExpStepCost]; omega
  have fuelEq : fuel+count+2+1 = fuel+count+3 := by omega
  rw [costEq,fuelEq] at exec
  rw [costEq] at bound
  refine ⟨restorePanValueFfiLocal name (production.locals name) result,
    {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_,?_⟩
  · simpa [word] using exec
  · simpa [word,expToHOL] using run
  · simpa [word,expToHOL] using bound
  · rw [resultEq]
    simp [restorePanValueFfiLocal,productionEntry]

/-- A fresh scalar declaration initializes the countdown local, and the
resulting loop-and-return body has the compiler's supported shape. -/
theorem counted_decl_countdown_return {σ : Type} (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64) (clock : count ≤ source.clock)
    (returned : BitVec 64) (ctxt : PanToCrepContextExact 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let program : Prog (RiscV.Word 64) := .dec name .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned))))
    let holProgram : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        production.locals production.globals production.memory production.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+9) ∧
      source.evaluateHOLFiniteState holProgram = (some (.returned (.val (.word returned))),final) ∧
      controlSteps holProgram source ≤ 6*count+9 ∧
      SteppedFlapjack.CrepToLoopSteps.SupportedCodeBody (compileProgExactHOLW ctxt holProgram) ∧
      result = .returned (restorePanValueLocal (fun _ => none) name (production.locals name))
        production.globals production.memory production.ffi [.word returned] := by
  let word := BitVec.ofNat 64 count
  let entry := setVarHOLFinite (ofString name) (.val (.word word)) source
  let productionEntry := {production with locals := updatePanValueMap production.locals name (.word word)}
  let entryDec : DecidablePred entry.memaddrs := by change DecidablePred source.memaddrs; infer_instance
  have entryRel : PanSemStateRelExec productionEntry entry.toExact := by
    simpa [productionEntry,entry] using PanSemStateRelExec.updateLocals rel name nameRanged (.word word)
  have entryRanged : PanSemStateRelExecRanged productionEntry := by
    exact PanSemStateRelExecRanged.updateLocals ranged name (.word word) (by simp [PanValueByteRanged])
  have initial : productionEntry.locals name = some (.word (BitVec.ofNat 64 count)) := by
    simp [productionEntry,word,updatePanValueMap]
  have entryClock : count ≤ entry.clock := by simpa [entry,setVarHOLFinite] using clock
  obtain ⟨result,final,bodyExec,bodyRun,bodyBound,resultEq⟩ := @counted_countdown_with_return σ count productionEntry entry entryDec
    entryRel entryRanged name nameRanged initial wordRange entryClock returned context primitive handler functions fuel
  have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+3)
      (updatePanValueMap production.locals name (.word word)) production.globals production.memory production.ffi
      (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+7) := by
    simpa [productionEntry,panSemBitVec64MemoryAccess] using bodyExec
  have initRun : evalPanSemStateExp production (.const word) = some (.word word) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
  obtain ⟨exec,run,bound⟩ := counted_decl_word production source final rel ranged name (.const word)
    (by simp [ExpByteRanged]) word initRun context primitive handler functions (fuel+count+3)
    (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned))))
    (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
    result (some (.returned (.val (.word returned)))) (6*count+7) bodyExec' bodyRun bodyBound
  have costEq : panValueExpStepCost (.const word : Exp (RiscV.Word 64)) + (6*count+7) + 1 = 6*count+9 := by
    simp [panValueExpStepCost]; omega
  have fuelEq : fuel+count+3+1 = fuel+count+4 := by omega
  rw [costEq,fuelEq] at exec
  rw [costEq] at bound
  refine ⟨restorePanValueFfiLocal name (production.locals name) result,
    {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_,?_,?_⟩
  · simpa [word] using exec
  · simpa [word,expToHOL] using run
  · simpa [word,expToHOL] using bound
  · have found := scalarDeclContext_local ctxt (ofString name)
    simpa [countdownBodyHOL] using scalarDeclLoop_supported ctxt (ofString name) (.const (BitVec.ofNat 64 count))
      (.var .local (ofString name)) .skip
      (.assign .local (ofString name) (.op .sub [.var .local (ofString name),.const 1])) (.return (.const returned))
      (.const _) .skip (.scalar (.local _ _ found)) (.assign _ _ found (.op .sub (.local _ _ found) (.const _))) (.return (.const _))
  · simpa [productionEntry,restorePanValueFfiLocal] using congrArg (restorePanValueFfiLocal name (production.locals name)) resultEq

/-- The counted countdown return supplies the original source run and a
source-count-dependent visit bound for the actual generated global entry. -/
theorem countdown_globalEntry_inputs {σ : Type} (count : Nat)
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (sourceClock : count ≤ source.clock) (returned : BitVec 64)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    ∃ result sourceFinal loweredFinal,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const (BitVec.ofNat 64 count))
          (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+9) ∧
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))) =
          (some (.returned (.val (.word returned))),sourceFinal) ∧
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty).evaluateHOLFiniteState
        (compileProgExactHOL globals (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
          (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) =
            (some (.returned (.val (.word returned))),loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal loweredFinal ∧
      globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL declarations) [] pan ≤
        controlSteps (nestedSeqHOL initializers) pan +
          (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
            sizeOf (compileProgExactHOL globals (countdownBodyHOL name)) +
            sizeOf (compileProgExactHOL globals (.return (.const returned)))) * (6*count+9) + 2 := by
  obtain ⟨result,sourceFinal,exec,run,bound,_,_⟩ := counted_decl_countdown_return count production source rel ranged
    name nameRanged wordRange sourceClock returned caller context primitive handler functions fuel
  let inner := scalarDeclContext caller (ofString name)
  have found := scalarDeclContext_local caller (ofString name)
  have bodyShape : BranchProgram inner (countdownBodyHOL name) := by
    exact .assign _ _ found (.op .sub (.local _ _ found) (.const _))
  obtain ⟨loweredFinal,_,loweredRun,postRel,entryBound⟩ := globalEntry_originalDeclLoop_with_steps
    declarations start initializers globals inner (ofString name) (.const (BitVec.ofNat 64 count)) .skip
    (.var .local (ofString name)) (countdownBodyHOL name) (.return (.const returned))
    .skip bodyShape (.return (.const _)) pan middle source sourceFinal
    (some (.returned (.val (.word returned)))) .one panCode initRun sourceFound entryClock run (by simp) globalRel
  refine ⟨result,sourceFinal,loweredFinal,exec,run,loweredRun,postRel,?_⟩
  have scaled := Nat.mul_le_mul_left
    (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
      sizeOf (compileProgExactHOL globals (countdownBodyHOL name)) +
      sizeOf (compileProgExactHOL globals (.return (.const returned)))) bound
  omega

/-- The actual counted countdown bounds the visits of its globally lowered,
compiled Crep body by a factor determined by the program's compiled shape. -/
theorem countdown_globalCrep_steps {σ : Type} (count : Nat)
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source lowered : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (crep : CrepSemHOLState 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (sourceClock : count ≤ source.clock) (returned : BitVec 64)
    (globalRel : panGlobalsStateRelHOLExact true globals source lowered)
    (stateRel : panToCrepStateRelFiniteExact lowered crep)
    (codeRel : codeRelExactHOLW ctxt lowered.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids lowered.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt lowered.locals crep.locals)
    (localised : localisedProgHOL (compileProgExactHOL globals
      (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) = true)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let body : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
    let inner := scalarDeclContext ctxt (ofString name)
    let factor := (4 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.skip))) +
      sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (countdownBodyHOL name))) +
      sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) *
      (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
        sizeOf (compileProgExactHOL globals (countdownBodyHOL name)) +
        sizeOf (compileProgExactHOL globals (.return (.const returned))))
    ∃ result sourceFinal loweredFinal crepResult crepFinal,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const (BitVec.ofNat 64 count))
          (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,6*count+9) ∧
      source.evaluateHOLFiniteState body = (some (.returned (.val (.word returned))),sourceFinal) ∧
      lowered.evaluateHOLFiniteState (compileProgExactHOL globals body) =
        (some (.returned (.val (.word returned))),loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal loweredFinal ∧
      evalCrepSemHOLProgExact crep (compileProgExactHOLW ctxt (compileProgExactHOL globals body)) = (crepResult,crepFinal) ∧
      panToCrepStateRelFiniteExact loweredFinal crepFinal ∧
      SteppedFlapjack.CrepToLoopSteps.CompleteCrepResult crepResult ∧
      pcCompileCorrectResultRel ctxt loweredFinal crepFinal (some (.returned (.val (.word returned)))) crepResult ∧
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW ctxt (compileProgExactHOL globals body)) crep ≤
        factor * (6*count+9) := by
  obtain ⟨result,sourceFinal,exec,run,bound,_,_⟩ := counted_decl_countdown_return count production source rel ranged
    name nameRanged wordRange sourceClock returned ctxt context primitive handler functions fuel
  let inner := scalarDeclContext ctxt (ofString name)
  have found := scalarDeclContext_local ctxt (ofString name)
  have bodyShape : BranchProgram inner (countdownBodyHOL name) := by
    exact .assign _ _ found (.op .sub (.local _ _ found) (.const _))
  have crepBound := globalCompile_declLoop_crep_steps globals ctxt (ofString name) (.const (BitVec.ofNat 64 count))
    .skip (.var .local (ofString name)) (countdownBodyHOL name) (.return (.const returned))
    (.const _) .skip (.local _ _ found) bodyShape (.return (.const _)) source sourceFinal lowered
    (some (.returned (.val (.word returned)))) crep run (by simp) globalRel stateRel codeRel excpRel localsRel localised
  let body : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
    (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
  obtain ⟨loweredFinal,loweredRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    body source (some (.returned (.val (.word returned)))) globals lowered sourceFinal ⟨globalRel,run,by simp⟩
  have correct : pcCompileCorrectAt (compileProgExactHOL globals body) lowered :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨crepResult,crepFinal,crepRun,finalRel,_,_,resultRel⟩ := correct
    (some (.returned (.val (.word returned)))) loweredFinal crep ctxt loweredRun (by simp)
    stateRel codeRel excpRel localsRel localised
  have complete : SteppedFlapjack.CrepToLoopSteps.CompleteCrepResult crepResult := by
    have resultEq := resultRel
    simp only [pcCompileCorrectResultRel] at resultEq
    rw [resultEq]
    exact .return _
  exact ⟨result,sourceFinal,loweredFinal,crepResult,crepFinal,exec,run,loweredRun,postRel,crepRun,finalRel,complete,resultRel,
    crepBound.trans (Nat.mul_le_mul_left _ bound)⟩

end SteppedFlapjack.PanToCrepSteps
