import SteppedFlapjack.PanToCrepSteps.CountedAssignLoop

/-! Recover source loop paths from counted executions. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A normal counted assignment must have evaluated its expression and passed
its dynamic assignment check. -/
theorem counted_assign_local_invert {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (assignment : Exp (RiscV.Word 64))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (localsPost : VarName → Option (PanValue (RiscV.Word 64))) (steps : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.assign .local name assignment)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
      some (.normal localsPost production.globals production.memory production.ffi,steps)) :
    ∃ value, evalPanSemStateExp production assignment = some value ∧
      panValueAssignmentValid production.structs production.locals production.globals .local name value = true ∧
      localsPost = updatePanValueMap production.locals name value ∧ steps = panValueExpStepCost assignment+1 := by
  have counted : evalPanValueExpCountedWith none production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord assignment
      (some (panSemBitVec64MemoryAccess production)) =
      (evalPanSemStateExp production assignment).map (fun value => (value,panValueExpStepCost assignment)) := by
    simp [evalPanValueExpCountedWith_eq_map,evalPanValueExpWith,evalPanSemStateExp_64_eq_previous]
  simp only [evalPanValueFfiProgSteps,panValueAssignLocalSteps,counted] at run
  cases eval : evalPanSemStateExp production assignment with
  | none => simp [eval] at run
  | some value =>
    simp only [eval,Option.map_some] at run
    cases valid : panValueAssignmentValid production.structs production.locals production.globals .local name value <;>
      simp_all

/-- The counted condition uses the ordinary expression value and its static
expression-step cost. -/
theorem counted_condition_eq {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (condition : Exp (RiscV.Word 64)) :
    panValueIteCondition production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
      production.locals production.globals production.memory condition (some (panSemBitVec64MemoryAccess production)) =
      match evalPanSemStateExp production condition with
      | some (.word word) => some (word,panValueExpStepCost condition)
      | _ => none := by
  simp only [panValueIteCondition,evalPanValueExpCounted,← evalPanSemStateExp_64_eq_previous]
  cases evalPanSemStateExp production condition with
  | none => rfl
  | some value => cases value <;> rfl

/-- A counted loop whose first condition is zero has the corresponding
zero-iteration path. -/
theorem assignLoopPath_zero_of_counted {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) (conditionRanged : ExpByteRanged condition)
    (cond : evalPanSemStateExp production condition = some (.word 0))
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (cost : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost)) :
    AssignLoopPath condition assignment name context primitive handler functions (fuel+1) production source finalLocals source cost := by
  simp [evalPanValueFfiProgSteps, counted_condition_eq,cond] at run
  rcases run with ⟨rfl,rfl⟩
  exact AssignLoopPath.zero fuel production source conditionRanged cond

/-- A nonzero first condition in a normally terminating counted loop exposes
a successful assignment and the remaining counted loop execution. -/
theorem counted_assignLoop_unroll {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (word : BitVec 64) (cond : evalPanSemStateExp production condition = some (.word word)) (nonzero : word ≠ 0)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (cost : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+2)
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost)) :
    ∃ value restCost,
      evalPanSemStateExp production assignment = some value ∧
      panValueAssignmentValid production.structs production.locals production.globals .local name value = true ∧
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
        (updatePanValueMap production.locals name value) production.globals production.memory production.ffi
        (.while condition (.assign .local name assignment))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.normal finalLocals production.globals production.memory production.ffi,restCost) ∧
      cost = panValueExpStepCost condition+(panValueExpStepCost assignment+1)+restCost+1 := by
  have counted : evalPanValueExpCountedWith none production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord assignment
      (some (panSemBitVec64MemoryAccess production)) =
      (evalPanSemStateExp production assignment).map (fun value => (value,panValueExpStepCost assignment)) := by
    simp [evalPanValueExpCountedWith_eq_map,evalPanValueExpWith,evalPanSemStateExp_64_eq_previous]
  rw [evalPanValueFfiProgSteps, counted_condition_eq,cond] at run
  simp only [Option.elim_some,beq_iff_eq,if_neg nonzero] at run
  cases evaluated : evalPanSemStateExp production assignment with
  | none =>
    have body : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
        production.locals production.globals production.memory production.ffi (.assign .local name assignment)
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.error production.locals production.globals production.memory production.ffi,0) := by
      simp [evalPanValueFfiProgSteps,panValueAssignLocalSteps,counted,evaluated]
    simp [body] at run
  | some value =>
    cases valid : panValueAssignmentValid production.structs production.locals production.globals .local name value with
    | false =>
      have body : evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
          production.locals production.globals production.memory production.ffi (.assign .local name assignment)
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
            some (.error production.locals production.globals production.memory production.ffi,panValueExpStepCost assignment+1) := by
        simp [evalPanValueFfiProgSteps,panValueAssignLocalSteps,counted,evaluated,valid]
      simp [body] at run
    | true =>
      have body : evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
          production.locals production.globals production.memory production.ffi (.assign .local name assignment)
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
            some (.normal (updatePanValueMap production.locals name value) production.globals production.memory production.ffi,
              panValueExpStepCost assignment+1) := by
        simp [evalPanValueFfiProgSteps,panValueAssignLocalSteps,counted,evaluated,valid]
      simp only [body] at run
      cases rest : evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
          (updatePanValueMap production.locals name value) production.globals production.memory production.ffi
          (.while condition (.assign .local name assignment))
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
      | none => simp [rest] at run
      | some result =>
        rcases result with ⟨result,restCost⟩
        cases result <;> simp_all

/-- Normal termination implies that the first loop condition evaluated to a word. -/
theorem counted_assignLoop_condition {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (cost : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost)) :
    ∃ word, evalPanSemStateExp production condition = some (.word word) := by
  rw [evalPanValueFfiProgSteps, counted_condition_eq] at run
  cases cond : evalPanSemStateExp production condition with
  | none => simp [cond] at run
  | some value => cases value <;> simp_all

/-- Every normally terminating assignment loop counts at least the final
condition evaluation and loop visit. -/
theorem counted_assignLoop_minCost {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    ∀ (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (cost : Nat),
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.normal finalLocals production.globals production.memory production.ffi,cost) →
      panValueExpStepCost condition+1 ≤ cost := by
  intro fuel
  induction fuel with
  | zero =>
    intro production finalLocals cost run
    simp [evalPanValueFfiProgSteps] at run
  | succ fuel ih =>
    intro production finalLocals cost run
    obtain ⟨word,cond⟩ := counted_assignLoop_condition condition assignment name context primitive handler functions
      fuel production finalLocals cost run
    by_cases zero : word = 0
    · subst word
      simp [evalPanValueFfiProgSteps,counted_condition_eq,cond] at run
      omega
    · cases fuel with
      | zero =>
        rw [evalPanValueFfiProgSteps,counted_condition_eq,cond] at run
        simp [evalPanValueFfiProgSteps] at run
        exact (zero (by simpa using run.1)).elim
      | succ fuel =>
        obtain ⟨value,restCost,_,_,restRun,costEq⟩ :=
          counted_assignLoop_unroll condition assignment name context primitive handler functions fuel production word cond zero
            finalLocals cost (by simpa [Nat.add_assoc] using run)
        let next := {production with locals := updatePanValueMap production.locals name value}
        have restMin := ih next finalLocals restCost (by simpa [next,panSemBitVec64MemoryAccess] using restRun)
        omega

/-- A normally terminating counted assignment loop yields its finite path
when the HOL clock covers the counted cost at the exact cost per iteration. -/
theorem assignLoopPath_of_counted {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) :
    ∀ (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ),
      PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production →
      ∀ (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (cost : Nat),
      cost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
        (panValueExpStepCost condition+1) →
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.normal finalLocals production.globals production.memory production.ffi,cost) →
      ∃ final, AssignLoopPath condition assignment name context primitive handler functions fuel production source finalLocals final cost := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro production source rel ranged finalLocals cost clock run
    simp [evalPanValueFfiProgSteps] at run
  | succ fuel ih =>
    intro production source rel ranged finalLocals cost clock run
    obtain ⟨word,cond⟩ := counted_assignLoop_condition condition assignment name context primitive handler functions
      fuel production finalLocals cost run
    by_cases zero : word = 0
    · subst word
      exact ⟨source,assignLoopPath_zero_of_counted condition assignment name context primitive handler functions
        fuel production source conditionRanged cond finalLocals cost run⟩
    · cases fuel with
      | zero =>
        rw [evalPanValueFfiProgSteps, counted_condition_eq,cond] at run
        simp [evalPanValueFfiProgSteps] at run
        exact (zero (by simpa using run.1)).elim
      | succ fuel =>
        obtain ⟨value,restCost,evaluated,validProd,restRun,costEq⟩ :=
          counted_assignLoop_unroll condition assignment name context primitive handler functions fuel production word cond zero
            finalLocals cost (by simpa [Nat.add_assoc] using run)
        let entry := source.decClockHOLFinite
        let pEntry := {production with clock := production.clock-1}
        let post := setVarHOLFinite (ofString name) (panValueToHOL value) entry
        let next := {production with locals := updatePanValueMap production.locals name value, clock := post.clock}
        have entryRel : PanSemStateRelExec pEntry entry.toExact := by
          simpa only [pEntry,entry,toExact_decClockHOLFinite] using PanSemStateRelExec.decClock rel
        have entryRanged : PanSemStateRelExecRanged pEntry := ranged.setClock _
        have assignmentRun : evalPanSemStateExp pEntry assignment = some value := by
          simpa [pEntry,evalPanSemStateExp_64_eq_previous,panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel] using evaluated
        have valueRanged := evalPanSemStateExp_byteRanged pEntry entryRanged assignment assignmentRanged value assignmentRun
        have parity := panValueAssignmentValid_eq_isValidValueHOLFinite pEntry entry entryRel entryRanged
          .local name nameRanged value valueRanged
        have valid : isValidValueHOLFinite entry .local (ofString name) (panValueToHOL value) = true := by
          rw [← parity]
          simpa [pEntry] using validProd
        obtain ⟨_,_,postRel,postRanged,_⟩ := counted_assign_local pEntry entry entryRel entryRanged
          name nameRanged assignment assignmentRanged value assignmentRun valid context primitive handler functions fuel
        have sameClock : post.clock = pEntry.clock := by
          have h := postRel.2.2.2.2.2.2.2.2.1
          simpa [post] using h
        have nextEq : next = {pEntry with locals := updatePanValueMap pEntry.locals name value} := by
          cases production
          simp_all [next,pEntry]
        have nextRel : PanSemStateRelExec next post.toExact := by rw [nextEq]; simpa [post] using postRel
        have nextRanged : PanSemStateRelExecRanged next := by rw [nextEq]; exact postRanged
        have restMin := counted_assignLoop_minCost condition assignment name context primitive handler functions
          (fuel+1) next finalLocals restCost (by simpa [next,panSemBitVec64MemoryAccess] using restRun)
        have sourceClock : source.clock ≠ 0 := by
          intro zeroClock
          rw [zeroClock] at clock
          simp only [Nat.zero_mul,Nat.zero_add] at clock
          omega
        have clockSucc : source.clock = (source.clock-1)+1 := by omega
        have clockMul : source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) =
            (source.clock-1)*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
              (panValueExpStepCost condition+panValueExpStepCost assignment+2) := by
          conv_lhs => rw [clockSucc]
          simp [Nat.add_mul]
        have nextClock : restCost ≤ post.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
            (panValueExpStepCost condition+1) := by
          simp [post,entry,setVarHOLFinite,decClockHOLFinite]
          omega
        obtain ⟨final,rest⟩ := ih next post nextRel nextRanged finalLocals restCost nextClock
          (by simpa [next,panSemBitVec64MemoryAccess] using restRun)
        refine ⟨final,?_⟩
        subst cost
        exact AssignLoopPath.step fuel production source final conditionRanged assignmentRanged nameRanged word cond zero
          sourceClock value (by simpa [pEntry] using assignmentRun) (by simpa [entry] using valid)
          finalLocals restCost (by simpa [next,post,entry] using rest)

/-- A successful counted assignment loop has a matching HOL execution whose
control visits are bounded by its actual counted source steps. -/
theorem counted_assignLoop_source_bound {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name)
    (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (cost : Nat)
    (clock : cost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
        (panValueExpStepCost condition+1))
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost)) :
    ∃ final, source.evaluateHOLFiniteState (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) =
        (none,final) ∧
      controlSteps (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) source ≤ cost := by
  obtain ⟨final,path⟩ := assignLoopPath_of_counted condition assignment name context primitive handler functions
    conditionRanged assignmentRanged nameRanged fuel production source rel ranged finalLocals cost clock run
  obtain ⟨_,holRun,bound⟩ := assignLoopPath_counted condition assignment name context primitive handler functions path rel ranged
  exact ⟨final,holRun,bound⟩

/-- A normal counted assignment loop and a source budget yield the actual
compiled Crep execution and its shape-dependent step bound. -/
theorem counted_assignLoop_crep_steps {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source : PanSemStateFiniteExact 64 σ}
    {finalLocals : VarName → Option (PanValue (RiscV.Word 64))} {cost : Nat}
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) (clock : cost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
        (panValueExpStepCost condition+1))
    (countedRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost))
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (budget : Nat) (budgetBound : cost ≤ budget)
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64)
    (conditionShape : ScalarExpression ctxt (expToHOL condition))
    (shape : BranchProgram ctxt (.assign .local (ofString name) (expToHOL assignment)))
    (lowered : PanSemStateFiniteExact 64 σ) (globalRel : panGlobalsStateRelHOLExact true globals source lowered)
    (crep : CrepSemHOLState 64 σ) (stateRel : panToCrepStateRelFiniteExact lowered crep)
    (codeRel : codeRelExactHOLW ctxt lowered.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids lowered.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt lowered.locals crep.locals)
    (localised : localisedProgHOL (compileProgExactHOL globals
      (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))) = true) :
    let body := ProgHOL.assign .local (ofString name) (expToHOL assignment)
    let loop := ProgHOL.while (expToHOL condition) body
    let loweredBody := compileProgExactHOL globals body
    let loweredLoop := compileProgExactHOL globals loop
    ∃ (final : PanSemStateFiniteExact 64 σ),
    source.evaluateHOLFiniteState loop = (none,final) ∧
    ∃ (loweredFinal : PanSemStateFiniteExact 64 σ) (crepResult : Option (CrepResultHOLExact 64)) (crepFinal : CrepSemHOLState 64 σ),
      lowered.evaluateHOLFiniteState loweredLoop = (none,loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (none : Option (PanSemResultExact 64))) globals final loweredFinal ∧
      evalCrepSemHOLProgExact crep (compileProgExactHOLW ctxt loweredLoop) = (crepResult,crepFinal) ∧
      panToCrepStateRelFiniteExact loweredFinal crepFinal ∧
      pcCompileCorrectResultRel ctxt loweredFinal crepFinal none crepResult ∧
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW ctxt loweredLoop) crep ≤
        (1 + sizeOf (compileProgExactHOLW ctxt loweredBody)) * (1 + sizeOf loweredBody) * budget := by
  obtain ⟨final,path⟩ := assignLoopPath_of_counted condition assignment name context primitive handler functions
    conditionRanged assignmentRanged nameRanged fuel production source rel ranged finalLocals cost clock countedRun
  obtain ⟨_,sourceRun,loweredFinal,crepResult,crepFinal,loweredRun,finalRel,crepRun,crepRel,resultRel,crepBound⟩ :=
    assignLoopPath_crep_steps condition assignment name context primitive handler functions path rel ranged budget budgetBound
      globals ctxt conditionShape shape lowered globalRel crep stateRel codeRel excpRel localsRel localised
  exact ⟨final,sourceRun,loweredFinal,crepResult,crepFinal,loweredRun,finalRel,crepRun,crepRel,resultRel,crepBound⟩

end SteppedFlapjack.PanToCrepSteps
