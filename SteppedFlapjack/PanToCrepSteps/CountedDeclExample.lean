import SteppedFlapjack.PanToCrepSteps.CountedDecl
import SteppedFlapjack.PanToCrepSteps.CountedLoopExample
import SteppedFlapjack.PanToCrepSteps.DeclLoopShape

/-! A complete counted declaration-wrapped loop example.

This module is a reusable proof component for the concrete source-to-machine
example, so it is imported by the library.
-/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A local initialized to one is set to zero by one loop iteration and a
constant is returned. The counted source run and HOL run agree, and the HOL
control-visit count is bounded by the actual counted cost. -/
theorem counted_decl_set_zero_with_tail {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (clock : source.clock ≠ 0)
    (returned : BitVec 64) (ctxt : PanToCrepContextExact 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let loop : Prog (RiscV.Word 64) := .while (.var .local name) (.assign .local name (.const 0))
    let program : Prog (RiscV.Word 64) := .dec name .one (.const 1) (.seq .skip (.seq loop (.return (.const returned))))
    let holLoop : ProgHOL 64 := .while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0))
    let holProgram : ProgHOL 64 := .dec (ofString name) .one (.const 1) (.seq .skip (.seq holLoop (.return (.const returned))))
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+7)
        production.locals production.globals production.memory production.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,13) ∧
      source.evaluateHOLFiniteState holProgram = (some (.returned (.val (.word returned))),final) ∧
      controlSteps holProgram source ≤ 13 ∧
      SteppedFlapjack.CrepToLoopSteps.SupportedCodeBody (compileProgExactHOLW ctxt holProgram) := by
  let p := {production with locals := updatePanValueMap production.locals name (.word (1 : BitVec 64))}
  let s := setVarHOLFinite (ofString name) (.val (.word 1)) source
  let sDec : DecidablePred s.memaddrs := by change DecidablePred source.memaddrs; infer_instance
  have pRel : PanSemStateRelExec p s.toExact := by
    simpa [p,s] using PanSemStateRelExec.updateLocals rel name nameRanged (.word (1 : BitVec 64))
  have pRanged : PanSemStateRelExecRanged p := by
    exact PanSemStateRelExecRanged.updateLocals ranged name (.word 1) (by simp [PanValueByteRanged])
  have initial : p.locals name = some (.word (1 : BitVec 64)) := by simp [p,updatePanValueMap]
  have clock' : s.clock ≠ 0 := by simpa [s,setVarHOLFinite] using clock
  obtain ⟨loopExec,loopRun,loopBound⟩ := @counted_while_set_zero_example σ p s sDec pRel pRanged name nameRanged
    1 (by decide) initial clock' context primitive handler functions (fuel+1)
  have localFound := scalarDeclContext_local ctxt (ofString name)
  obtain ⟨_,_,_,_,bodyRun,bodyBound⟩ := @counted_set_zero_with_tail σ p s sDec pRel pRanged name nameRanged
    1 (by decide) initial clock' returned (scalarDeclContext ctxt (ofString name)) (ctxt.vmax+1) localFound
    context primitive handler functions (fuel+2)
  let result : PanValueFfiControlResult (RiscV.Word 64) σ :=
    .returned (fun _ => none) production.globals production.memory production.ffi [.word returned]
  have bodyExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+6)
      (updatePanValueMap production.locals name (.word 1)) production.globals production.memory production.ffi
      (.seq .skip (.seq (.while (.var .local name) (.assign .local name (.const 0))) (.return (.const returned))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,11) := by
    have hloop : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+4)
        (updatePanValueMap production.locals name (.word 1)) production.globals production.memory production.ffi
        (.while (.var .local name) (.assign .local name (.const 0)))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal (updatePanValueMap (updatePanValueMap production.locals name (.word 1)) name (.word 0))
          production.globals production.memory production.ffi,6) := by
      simpa [p,panSemBitVec64MemoryAccess,Nat.add_assoc] using loopExec
    have inner : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+5)
        (updatePanValueMap production.locals name (.word 1)) production.globals production.memory production.ffi
        (.seq (.while (.var .local name) (.assign .local name (.const 0))) (.return (.const returned)))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,9) := by
      rw [evalPanValueFfiProgSteps]
      rw [hloop]
      simp [evalPanValueFfiProgSteps,panValueReturnResult,evalPanValueExpCounted,
        evalPanValueExp,panValueExpStepCost,panValuePayloadWithinLimit,panValuePayloadSizeFuel,result]
    have skipExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+5)
        (updatePanValueMap production.locals name (.word 1)) production.globals production.memory production.ffi
        .skip (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal (updatePanValueMap production.locals name (.word 1)) production.globals production.memory production.ffi,1) := by
      rw [evalPanValueFfiProgSteps]
    rw [evalPanValueFfiProgSteps,skipExec]
    simp only [bind, Option.bind]
    rw [inner]
    rfl
  have initializerRun : evalPanSemStateExp production (.const 1) = some (.word 1) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
  obtain ⟨exec,run,bound⟩ := counted_decl_word production source (emptyLocalsHOLFinite (setVarHOLFinite (ofString name) (.val (.word 0)) s.decClockHOLFinite)) rel ranged name (.const 1) (by simp [ExpByteRanged])
    1 initializerRun context primitive handler functions (fuel+6)
    (.seq .skip (.seq (.while (.var .local name) (.assign .local name (.const 0))) (.return (.const returned))))
    (.seq .skip (.seq (.while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0))) (.return (.const returned))))
    result (some (.returned (.val (.word returned)))) 11 bodyExec bodyRun (by simpa [s] using Nat.le_trans bodyBound (by decide))
  dsimp only
  let final := emptyLocalsHOLFinite (setVarHOLFinite (ofString name) (.val (.word 0)) s.decClockHOLFinite)
  refine ⟨restorePanValueFfiLocal name (production.locals name) result,
    {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_,?_⟩
  · simpa [panValueExpStepCost] using exec
  · simpa only [expToHOL,final] using run
  · simpa [expToHOL,panValueExpStepCost] using bound
  · exact scalarDeclLoop_set_zero_supported ctxt (ofString name) returned

end SteppedFlapjack.PanToCrepSteps
