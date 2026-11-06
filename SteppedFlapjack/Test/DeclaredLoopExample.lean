import SteppedFlapjack.PanToCrepSteps.CountedDeclaredAssignLoop
import SteppedFlapjack.PanToCrepSteps.CountedCountdown

/-! A nonzero iteration through the generalized declared-loop source proof. -/
namespace SteppedFlapjack.Test
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

/-- A declared countdown starting at one executes one assignment iteration;
the generalized declaration theorem proves its actual counted source run. -/
theorem declared_countdown_one {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (sourceClock : 1 ≤ source.clock)
    (returned : BitVec 64) (ctxt : PanToCrepContextExact 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord 5
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const 1) (.seq .skip (.seq
          (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,15) ∧
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const 1) (.seq .skip (.seq
        (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))) =
          (some (.returned (.val (.word returned))),final) := by
  let entry := setVarHOLFinite (ofString name) (.val (.word 1)) source
  let productionEntry := {production with locals := updatePanValueMap production.locals name (.word 1)}
  let entryDec : DecidablePred entry.memaddrs := by change DecidablePred source.memaddrs; infer_instance
  have entryRel : PanSemStateRelExec productionEntry entry.toExact := by
    simpa [productionEntry,entry] using PanSemStateRelExec.updateLocals rel name nameRanged (.word 1)
  have entryRanged : PanSemStateRelExecRanged productionEntry := by
    exact PanSemStateRelExecRanged.updateLocals ranged name (.word 1) (by simp [PanValueByteRanged])
  have initial : productionEntry.locals name = some (.word (BitVec.ofNat 64 1)) := by simp [productionEntry,updatePanValueMap]
  have entryClock : 1 ≤ entry.clock := by simpa [entry,setVarHOLFinite] using sourceClock
  obtain ⟨finalLocals,_,loopExec,_,_,_,_⟩ := @counted_countdown σ 1 productionEntry entry entryDec entryRel entryRanged
    name nameRanged initial (by decide) entryClock context primitive handler functions 0
  have loopExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord 2
      (updatePanValueMap production.locals name (.word 1)) production.globals production.memory production.ffi
      (.while (.var .local name) (countdownBody name))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,8) := by
    simpa [productionEntry,panSemBitVec64MemoryAccess] using loopExec
  have found := scalarDeclContext_local ctxt (ofString name)
  obtain ⟨result,final,exec,run,_,_⟩ := counted_declared_assignLoop_return
    (.var .local name) (.op .sub [.var .local name,.const 1]) name 1 returned context primitive handler functions
    (by simpa [ExpByteRanged] using nameRanged)
    (by simpa [ExpByteRanged,ListExpByteRanged] using nameRanged) nameRanged 1 production source rel ranged finalLocals 8
    (by simp [panValueExpStepCost,panValueExpStepCost.panValueExpsStepCost]; omega)
    (by simpa [countdownBody] using loopExec') ctxt
    (by simpa [expToHOL] using (ScalarExpression.local _ _ found))
    (by simpa [expToHOL] using (BranchProgram.assign _ _ found (.op .sub (.local _ _ found) (.const _))))
  exact ⟨result,final,by simpa [countdownBody] using exec,by simpa [countdownBodyHOL,expToHOL] using run⟩

end SteppedFlapjack.Test
