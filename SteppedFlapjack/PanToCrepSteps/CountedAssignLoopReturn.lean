import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopInvert
import SteppedFlapjack.PanToCrepSteps.GlobalSourceEntry

/-! Complete assignment-loop source executions and their return tails. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- An assignment-loop path preserves the executable/HOL relation and
byte-ranged invariants at its final state. -/
theorem assignLoopPath_final_rel {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source final : PanSemStateFiniteExact 64 σ}
    {finalLocals : VarName → Option (PanValue (RiscV.Word 64))} {cost : Nat}
    (path : AssignLoopPath condition assignment name context primitive handler functions fuel production source finalLocals final cost) :
    PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production →
    PanSemStateRelExec {production with locals := finalLocals, clock := final.clock} final.toExact ∧
    PanSemStateRelExecRanged {production with locals := finalLocals, clock := final.clock} := by
  classical
  induction path with
  | zero fuel production source conditionRanged conditionRun =>
    intro rel ranged
    have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
    exact ⟨by simpa [clockEq] using rel,by simpa [clockEq] using ranged⟩
  | step fuel production source final conditionRanged assignmentRanged nameRanged word conditionRun nonzero clock
      value assignmentRun valid finalLocals restCost rest ih =>
    intro rel ranged
    let entry := source.decClockHOLFinite
    let pEntry := {production with clock := production.clock-1}
    let post := setVarHOLFinite (ofString name) (panValueToHOL value) entry
    let next := {production with locals := updatePanValueMap production.locals name value, clock := post.clock}
    have entryRel : PanSemStateRelExec pEntry entry.toExact := by
      simpa only [pEntry,entry,toExact_decClockHOLFinite] using PanSemStateRelExec.decClock rel
    have entryRanged : PanSemStateRelExecRanged pEntry := ranged.setClock _
    have valueRanged := evalPanSemStateExp_byteRanged pEntry entryRanged assignment assignmentRanged value assignmentRun
    have postRel := PanSemStateRelExec.updateLocals entryRel name nameRanged value
    have postRanged := PanSemStateRelExecRanged.updateLocals entryRanged name value valueRanged
    have sameClock : post.clock = pEntry.clock := by
      have h := postRel.2.2.2.2.2.2.2.2.1
      simpa [post] using h
    have nextEq : next = {pEntry with locals := updatePanValueMap pEntry.locals name value} := by
      cases production
      simp_all [next,pEntry]
    have nextRel : PanSemStateRelExec next post.toExact := by rw [nextEq]; simpa [post] using postRel
    have nextRanged : PanSemStateRelExecRanged next := by rw [nextEq]; exact postRanged
    have finalRel := ih (by simpa [next,post,entry] using nextRel) (by simpa [next,post,entry] using nextRanged)
    simpa [next] using finalRel

/-- A normally terminating counted assignment loop followed by a constant
return has a matching HOL execution and costs five more source steps, including
the leading skip and both sequence nodes. -/
theorem counted_assignLoop_with_return {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (clock : fuel+1 ≤ source.clock+1)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (loopCost : Nat) (returned : BitVec 64)
    (loopExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,loopCost)) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
        production.locals production.globals production.memory production.ffi
        (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,loopCost+5) ∧
      source.evaluateHOLFiniteState (.seq .skip (.seq (.while (expToHOL condition)
        (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))) =
        (some (.returned (.val (.word returned))),final) ∧
      controlSteps (.seq .skip (.seq (.while (expToHOL condition)
        (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))) source ≤ loopCost+5 := by
  classical
  obtain ⟨middle,path⟩ := assignLoopPath_of_counted condition assignment name context primitive handler functions
    conditionRanged assignmentRanged nameRanged (fuel+1) production source rel ranged clock finalLocals loopCost loopExec
  obtain ⟨_,loopRun,loopBound⟩ := assignLoopPath_counted condition assignment name context primitive handler functions path rel ranged
  obtain ⟨middleRel,middleRanged⟩ := assignLoopPath_final_rel condition assignment name context primitive handler functions path rel ranged
  let middleProduction := {production with locals := finalLocals, clock := middle.clock}
  obtain ⟨returnExec,returnRun,_,returnBound⟩ := counted_return_word_related middleProduction middle middleRel middleRanged
    (.const returned) (by simp [ExpByteRanged]) returned (by simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp])
    context primitive handler functions fuel
  have returnExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      finalLocals production.globals production.memory production.ffi (.return (.const returned))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned (fun _ => none) production.globals production.memory production.ffi [.word returned],2) := by
    simpa [middleProduction,panSemBitVec64MemoryAccess,panValueExpStepCost] using returnExec
  obtain ⟨innerExec,innerRun,innerBound⟩ := counted_seq_normal context primitive handler production.structs functions
    production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
    production.locals production.globals production.memory production.ffi
    finalLocals production.globals production.memory production.ffi
    (.while condition (.assign .local name assignment)) (.return (.const returned))
    (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))
    (some (panSemBitVec64MemoryAccess production)) none none
    (.returned (fun _ => none) production.globals production.memory production.ffi [.word returned])
    loopCost 2 source middle (emptyLocalsHOLFinite middle) (some (.returned (.val (.word returned))))
    loopExec returnExec' loopRun (by simpa [expToHOL] using returnRun) loopBound (by simpa [expToHOL,panValueExpStepCost] using returnBound)
  have skipExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+2)
      production.locals production.globals production.memory production.ffi .skip
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal production.locals production.globals production.memory production.ffi,1) := by
    rw [evalPanValueFfiProgSteps]
  have skipBound : controlSteps (.skip : ProgHOL 64) source ≤ 1 := by rw [controlSteps.eq_def]; rfl
  obtain ⟨exec,run,bound⟩ := counted_seq_normal context primitive handler production.structs functions
    production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+2)
    production.locals production.globals production.memory production.ffi
    production.locals production.globals production.memory production.ffi .skip
    (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))
    (.skip : ProgHOL 64) (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))
    (some (panSemBitVec64MemoryAccess production)) none none
    (.returned (fun _ => none) production.globals production.memory production.ffi [.word returned])
    1 (loopCost+2+1) source source (emptyLocalsHOLFinite middle) (some (.returned (.val (.word returned))))
    skipExec innerExec (evaluateHOLFiniteState_skip source) innerRun skipBound innerBound
  have costEq : 1+(loopCost+2+1)+1 = loopCost+5 := by omega
  have fuelEq : fuel+2+1 = fuel+3 := by omega
  rw [costEq,fuelEq] at exec
  rw [costEq] at bound
  exact ⟨_,_,exec,run,bound⟩

/-- The normal counted loop and return determine the actual lowered entry
execution and bound its visits by a separately supplied source budget. -/
theorem counted_assignLoop_globalEntry {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (clock : fuel+1 ≤ source.clock+1)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (loopCost budget : Nat) (returned : BitVec 64)
    (budgetBound : loopCost+5 ≤ budget)
    (loopExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,loopCost))
    (conditionShape : ScalarExpression caller (expToHOL condition))
    (bodyShape : BranchProgram caller (.assign .local (ofString name) (expToHOL assignment)))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))
        (.return (.const returned))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty)) :
    let body := ProgHOL.assign .local (ofString name) (expToHOL assignment)
    let program := ProgHOL.seq .skip (.seq (.while (expToHOL condition) body) (.return (.const returned)))
    ∃ result sourceFinal loweredFinal,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
        production.locals production.globals production.memory production.ffi
        (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,loopCost+5) ∧
      source.evaluateHOLFiniteState program = (some (.returned (.val (.word returned))),sourceFinal) ∧
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty).evaluateHOLFiniteState
        (compileProgExactHOL globals program) = (some (.returned (.val (.word returned))),loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal loweredFinal ∧
      globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL declarations) [] pan ≤
        controlSteps (nestedSeqHOL initializers) pan +
          (3 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
            sizeOf (compileProgExactHOL globals body) +
            sizeOf (compileProgExactHOL globals (.return (.const returned)))) * budget + 2 := by
  obtain ⟨result,sourceFinal,exec,run,bound⟩ := counted_assignLoop_with_return condition assignment name context primitive handler
    functions conditionRanged assignmentRanged nameRanged fuel production source rel ranged clock finalLocals loopCost returned loopExec
  obtain ⟨loweredFinal,_,_,_,_,_,loweredRun,postRel,entryBound⟩ := globalEntry_originalLoop_with_steps
    declarations start initializers globals caller .skip (expToHOL condition)
    (.assign .local (ofString name) (expToHOL assignment)) (.return (.const returned))
    .skip conditionShape bodyShape (.return (.const _)) pan middle source sourceFinal
    (some (.returned (.val (.word returned)))) .one panCode initRun sourceFound entryClock run (by simp) globalRel
  refine ⟨result,sourceFinal,loweredFinal,exec,run,?_,postRel,?_⟩
  · simpa only [compileProgExactHOL] using loweredRun
  · have sourceBound := bound.trans budgetBound
    have scaled := Nat.mul_le_mul_left
      (3 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
        sizeOf (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) sourceBound
    omega

end SteppedFlapjack.PanToCrepSteps
