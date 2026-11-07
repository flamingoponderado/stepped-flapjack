import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopReturn
import SteppedFlapjack.PanToCrepSteps.DeclLoopShape
import SteppedFlapjack.PanToCrepSteps.CountedDecl
import SteppedFlapjack.PanToCrepSteps.GlobalDecl

/-! Counted assignment loops with a local initialized at the source entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A scalar declaration initializes the loop local before an arbitrary
supported assignment loop and constant return. -/
theorem counted_declared_assignLoop_return {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName) (initial returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (loopCost : Nat)
    (clock : loopCost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1))
    (loopExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      (updatePanValueMap production.locals name (.word initial)) production.globals production.memory production.ffi
      (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,loopCost))
    (ctxt : PanToCrepContextExact 64)
    (conditionShape : ScalarExpression (scalarDeclContext ctxt (ofString name)) (expToHOL condition))
    (bodyShape : BranchProgram (scalarDeclContext ctxt (ofString name))
      (.assign .local (ofString name) (expToHOL assignment))) :
    let program := Prog.dec name .one (.const initial)
      (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
    let holProgram := ProgHOL.dec (ofString name) .one (.const initial)
      (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+4)
        production.locals production.globals production.memory production.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,loopCost+7) ∧
      source.evaluateHOLFiniteState holProgram = (some (.returned (.val (.word returned))),final) ∧
      controlSteps holProgram source ≤ loopCost+7 ∧
      SteppedFlapjack.CrepToLoopSteps.SupportedCodeBody (compileProgExactHOLW ctxt holProgram) := by
  let entry := setVarHOLFinite (ofString name) (.val (.word initial)) source
  let productionEntry := {production with locals := updatePanValueMap production.locals name (.word initial)}
  let entryDec : DecidablePred entry.memaddrs := by change DecidablePred source.memaddrs; infer_instance
  have entryRel : PanSemStateRelExec productionEntry entry.toExact := by
    simpa [productionEntry,entry] using PanSemStateRelExec.updateLocals rel name nameRanged (.word initial)
  have entryRanged : PanSemStateRelExecRanged productionEntry := by
    exact PanSemStateRelExecRanged.updateLocals ranged name (.word initial) (by simp [PanValueByteRanged])
  have entryClock : loopCost ≤ entry.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1) := by simpa [entry,setVarHOLFinite] using clock
  have entryExec : evalPanValueFfiProgSteps context primitive handler productionEntry.structs functions
      productionEntry.baseAddress productionEntry.topAddress panSemBitVec64BytesInWord (fuel+1)
      productionEntry.locals productionEntry.globals productionEntry.memory productionEntry.ffi
      (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess productionEntry)) =
        some (.normal finalLocals productionEntry.globals productionEntry.memory productionEntry.ffi,loopCost) := by
    simpa [productionEntry,panSemBitVec64MemoryAccess] using loopExec
  obtain ⟨result,final,bodyExec,bodyRun,bodyBound⟩ := @counted_assignLoop_with_return σ condition assignment name
    context primitive handler functions conditionRanged assignmentRanged nameRanged fuel productionEntry entry entryRel entryRanged
    finalLocals loopCost returned entryClock entryExec
  have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
      (updatePanValueMap production.locals name (.word initial)) production.globals production.memory production.ffi
      (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,loopCost+5) := by
    simpa [productionEntry,panSemBitVec64MemoryAccess] using bodyExec
  have initRun : evalPanSemStateExp production (.const initial) = some (.word initial) := by
    simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
  obtain ⟨exec,run,bound⟩ := counted_decl_word production source final rel ranged name (.const initial)
    (by simp [ExpByteRanged]) initial initRun context primitive handler functions (fuel+3)
    (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
    (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))
    result (some (.returned (.val (.word returned)))) (loopCost+5) bodyExec' bodyRun bodyBound
  have costEq : panValueExpStepCost (.const initial : Exp (RiscV.Word 64)) + (loopCost+5) + 1 = loopCost+7 := by
    simp [panValueExpStepCost]; omega
  have fuelEq : fuel+3+1 = fuel+4 := by omega
  rw [costEq,fuelEq] at exec
  rw [costEq] at bound
  refine ⟨restorePanValueFfiLocal name (production.locals name) result,
    {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_,?_⟩
  · simpa [expToHOL] using exec
  · simpa [expToHOL] using run
  · simpa [expToHOL] using bound
  · exact scalarDeclLoop_supported ctxt (ofString name) (.const initial) (expToHOL condition) .skip
      (.assign .local (ofString name) (expToHOL assignment)) (.return (.const returned))
      (.const _) .skip (.scalar conditionShape) bodyShape (.return (.const _))

/-- The declared assignment-loop source bounds the actual global entry by a
separately supplied source-step budget. -/
theorem counted_declared_assignLoop_globalEntry {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName) (initial returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (loopCost budget : Nat)
    (clock : loopCost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1)) (budgetBound : loopCost+7 ≤ budget)
    (loopExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      (updatePanValueMap production.locals name (.word initial)) production.globals production.memory production.ffi
      (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,loopCost))
    (conditionShape : ScalarExpression (scalarDeclContext caller (ofString name)) (expToHOL condition))
    (bodyShape : BranchProgram (scalarDeclContext caller (ofString name))
      (.assign .local (ofString name) (expToHOL assignment)))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty)) :
    let body := ProgHOL.assign .local (ofString name) (expToHOL assignment)
    let program := ProgHOL.dec (ofString name) .one (.const initial)
      (.seq .skip (.seq (.while (expToHOL condition) body) (.return (.const returned))))
    ∃ result sourceFinal loweredFinal,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const initial) (.seq .skip (.seq
          (.while condition (.assign .local name assignment)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,loopCost+7) ∧
      source.evaluateHOLFiniteState program = (some (.returned (.val (.word returned))),sourceFinal) ∧
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty).evaluateHOLFiniteState
        (compileProgExactHOL globals program) = (some (.returned (.val (.word returned))),loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal loweredFinal ∧
      globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL declarations) [] pan ≤
        controlSteps (nestedSeqHOL initializers) pan +
          (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
            sizeOf (compileProgExactHOL globals body) +
            sizeOf (compileProgExactHOL globals (.return (.const returned)))) * budget + 2 := by
  obtain ⟨result,sourceFinal,exec,run,bound,_⟩ := counted_declared_assignLoop_return condition assignment name initial returned
    context primitive handler functions conditionRanged assignmentRanged nameRanged fuel production source rel ranged
    finalLocals loopCost clock loopExec caller conditionShape bodyShape
  obtain ⟨loweredFinal,_,loweredRun,postRel,entryBound⟩ := globalEntry_originalDeclLoop_with_steps
    declarations start initializers globals (scalarDeclContext caller (ofString name)) (ofString name) (.const initial) .skip
    (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)) (.return (.const returned))
    .skip bodyShape (.return (.const _)) pan middle source sourceFinal
    (some (.returned (.val (.word returned)))) .one panCode initRun sourceFound entryClock run (by simp) globalRel
  refine ⟨result,sourceFinal,loweredFinal,exec,run,loweredRun,postRel,?_⟩
  have sourceBound := bound.trans budgetBound
  have scaled := Nat.mul_le_mul_left
    (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
      sizeOf (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))) +
      sizeOf (compileProgExactHOL globals (.return (.const returned)))) sourceBound
  omega

end SteppedFlapjack.PanToCrepSteps
