import SteppedFlapjack.PanToCrepSteps.CountedWhileTrace
import SteppedFlapjack.PanToCrepSteps.CountedAssign
import SteppedFlapjack.PanToCrepSteps.GlobalWhile

/-! Counted loops with arbitrary local-assignment bodies. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A finite path through a loop whose body is one local assignment. The path
records expression evaluations and assignment validity; body executions and
body cost bounds are derived rather than stored. -/
inductive AssignLoopPath {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    Nat → PanSemState (RiscV.Word 64) (FfiState σ) → PanSemStateFiniteExact 64 σ →
      (VarName → Option (PanValue (RiscV.Word 64))) → PanSemStateFiniteExact 64 σ → Nat → Prop where
  | zero (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ)
      (conditionRanged : ExpByteRanged condition)
      (conditionRun : evalPanSemStateExp production condition = some (.word 0)) :
      AssignLoopPath condition assignment name context primitive handler functions (fuel+1) production source
        production.locals source (panValueExpStepCost condition+1)
  | step (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source final : PanSemStateFiniteExact 64 σ)
      (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
      (nameRanged : NameRanged name) (word : BitVec 64)
      (conditionRun : evalPanSemStateExp production condition = some (.word word))
      (nonzero : word ≠ 0) (clock : source.clock ≠ 0) (value : PanValue (RiscV.Word 64))
      (assignmentRun : evalPanSemStateExp {production with clock := production.clock-1} assignment = some value)
      (valid : isValidValueHOLFinite source.decClockHOLFinite .local (ofString name) (panValueToHOL value) = true)
      (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (restCost : Nat)
      (rest : AssignLoopPath condition assignment name context primitive handler functions (fuel+1)
        {production with locals := updatePanValueMap production.locals name value, clock := (setVarHOLFinite (ofString name) (panValueToHOL value) source.decClockHOLFinite).clock}
        (setVarHOLFinite (ofString name) (panValueToHOL value) source.decClockHOLFinite) finalLocals final restCost) :
      AssignLoopPath condition assignment name context primitive handler functions (fuel+2) production source
        finalLocals final (panValueExpStepCost condition+(panValueExpStepCost assignment+1)+restCost+1)

/-- The counted cost and HOL clock decrease of an assignment-loop path
are both determined by the same number of loop iterations. -/
theorem assignLoopPath_cost_clock {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source final : PanSemStateFiniteExact 64 σ}
    {finalLocals : VarName → Option (PanValue (RiscV.Word 64))} {cost : Nat}
    (path : AssignLoopPath condition assignment name context primitive handler functions fuel production source finalLocals final cost) :
    ∃ iterations,
      cost = (panValueExpStepCost condition+1) +
        iterations*(panValueExpStepCost condition+panValueExpStepCost assignment+2) ∧
      source.clock = final.clock+iterations := by
  induction path with
  | zero => exact ⟨0,by simp,by simp⟩
  | step fuel production source final conditionRanged assignmentRanged nameRanged word conditionRun nonzero clock
      value assignmentRun valid finalLocals restCost rest ih =>
    obtain ⟨iterations,costEq,clockEq⟩ := ih
    refine ⟨iterations+1,?_,?_⟩
    · rw [Nat.add_mul]
      simp only [Nat.one_mul]
      omega
    · simp [setVarHOLFinite,decClockHOLFinite] at clockEq
      omega

/-- The iteration-based clock condition is necessary for every complete
assignment-loop path. -/
theorem assignLoopPath_clock_bound {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source final : PanSemStateFiniteExact 64 σ}
    {finalLocals : VarName → Option (PanValue (RiscV.Word 64))} {cost : Nat}
    (path : AssignLoopPath condition assignment name context primitive handler functions fuel production source finalLocals final cost) :
    cost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1) := by
  obtain ⟨iterations,costEq,clockEq⟩ := assignLoopPath_cost_clock condition assignment name context primitive handler functions path
  have iterationsBound : iterations ≤ source.clock := by omega
  have scaled := Nat.mul_le_mul_right (panValueExpStepCost condition+panValueExpStepCost assignment+2) iterationsBound
  omega

/-- Assignment-loop paths produce the actual counted and HOL loop executions,
with the HOL control visits bounded by the counted source steps. -/
theorem assignLoopPath_counted {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source final : PanSemStateFiniteExact 64 σ}
    {finalLocals : VarName → Option (PanValue (RiscV.Word 64))} {cost : Nat}
    (path : AssignLoopPath condition assignment name context primitive handler functions fuel production source finalLocals final cost)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost) ∧
    source.evaluateHOLFiniteState (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) = (none,final) ∧
    controlSteps (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) source ≤ cost := by
  classical
  have tracedAux : PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production →
    CountedWhileTrace condition (.assign .local name assignment)
      (.assign .local (ofString name) (expToHOL assignment)) context primitive handler functions
      fuel production source (.normal finalLocals production.globals production.memory production.ffi) none final cost := by
    induction path with
    | zero fuel production source conditionRanged conditionRun =>
      intro rel ranged
      exact .zero fuel production source rel ranged conditionRanged conditionRun
    | step fuel production source final conditionRanged assignmentRanged nameRanged word conditionRun nonzero clock
        value assignmentRun valid finalLocals restCost rest ih =>
      intro rel ranged
      let entry := source.decClockHOLFinite
      let pEntry := {production with clock := production.clock-1}
      let post := setVarHOLFinite (ofString name) (panValueToHOL value) entry
      have entryRel : PanSemStateRelExec pEntry entry.toExact := by
        simpa only [pEntry,entry,toExact_decClockHOLFinite] using PanSemStateRelExec.decClock rel
      have entryRanged : PanSemStateRelExecRanged pEntry := ranged.setClock _
      obtain ⟨bodyExec,bodyRun,postRel,postRanged,bodyBound⟩ :=
        counted_assign_local pEntry entry entryRel entryRanged name nameRanged assignment assignmentRanged value
          assignmentRun valid context primitive handler functions fuel
      have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
          production.locals production.globals production.memory production.ffi (.assign .local name assignment)
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.normal (updatePanValueMap production.locals name value) production.globals production.memory production.ffi,
            panValueExpStepCost assignment+1) := by
        simpa [pEntry,panSemBitVec64MemoryAccess] using bodyExec
      have sameClock : post.clock = pEntry.clock := by
        have h := postRel.2.2.2.2.2.2.2.2.1
        simpa [post] using h
      have nextEq : {production with locals := updatePanValueMap production.locals name value, clock := post.clock} =
          {pEntry with locals := updatePanValueMap pEntry.locals name value} := by
        cases production
        simp_all [pEntry]
      have nextRel : PanSemStateRelExec
          {production with locals := updatePanValueMap production.locals name value, clock := post.clock} post.toExact := by
        rw [nextEq]
        simpa [post] using postRel
      have nextRanged : PanSemStateRelExecRanged
          {production with locals := updatePanValueMap production.locals name value, clock := post.clock} := by
        rw [nextEq]
        exact postRanged
      have tracedRest := ih (by simpa [entry,post] using nextRel) (by simpa [entry,post] using nextRanged)
        (by simpa [entry,post] using nextRel) (by simpa [entry,post] using nextRanged)
      simpa [entry,post] using
        (CountedWhileTrace.iteration (fuel+1) production source post final rel ranged conditionRanged word conditionRun
          nonzero clock (updatePanValueMap production.locals name value) production.globals production.memory production.ffi
          false (panValueExpStepCost assignment+1) restCost (.normal finalLocals production.globals production.memory production.ffi)
          none (by simpa using bodyExec') (by simpa [entry,post] using bodyRun)
          (by simpa [entry] using bodyBound) (by simpa [entry,post] using tracedRest))
  exact counted_while_trace condition (.assign .local name assignment) _ context primitive handler functions (tracedAux rel ranged)

/-- A separately supplied source-step budget bounds the actual globals-lowered
loop for any supported assignment loop with a finite path. -/
theorem assignLoopPath_global_steps {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source final : PanSemStateFiniteExact 64 σ}
    {finalLocals : VarName → Option (PanValue (RiscV.Word 64))} {cost : Nat}
    (path : AssignLoopPath condition assignment name context primitive handler functions fuel production source finalLocals final cost)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (budget : Nat) (budgetBound : cost ≤ budget)
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64)
    (shape : BranchProgram ctxt (.assign .local (ofString name) (expToHOL assignment)))
    (lowered : PanSemStateFiniteExact 64 σ) (globalRel : panGlobalsStateRelHOLExact true globals source lowered) :
    let body := ProgHOL.assign .local (ofString name) (expToHOL assignment)
    let loop := ProgHOL.while (expToHOL condition) body
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost) ∧
    source.evaluateHOLFiniteState loop = (none,final) ∧
    ∃ (loweredFinal : PanSemStateFiniteExact 64 σ),
      lowered.evaluateHOLFiniteState (compileProgExactHOL globals loop) = (none,loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (none : Option (PanSemResultExact 64))) globals final loweredFinal ∧
      controlSteps (compileProgExactHOL globals loop) lowered ≤
        (1 + sizeOf (compileProgExactHOL globals body)) * budget := by
  obtain ⟨exec,run,sourceBound⟩ := assignLoopPath_counted condition assignment name context primitive handler functions path rel ranged
  obtain ⟨loweredFinal,loweredRun,finalRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))
    source none globals lowered final ⟨globalRel,run,by simp⟩
  have loweredBound := globalCompile_while_steps globals ctxt (expToHOL condition)
    (.assign .local (ofString name) (expToHOL assignment)) shape source final lowered none run (by simp) globalRel
  exact ⟨exec,run,loweredFinal,loweredRun,finalRel,loweredBound.trans (Nat.mul_le_mul_left _ (sourceBound.trans budgetBound))⟩

/-- A finite assignment-loop path yields the actual compiled Crep execution
and a compiler-shape-dependent bound in the supplied source-step budget. -/
theorem assignLoopPath_crep_steps {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source final : PanSemStateFiniteExact 64 σ}
    {finalLocals : VarName → Option (PanValue (RiscV.Word 64))} {cost : Nat}
    (path : AssignLoopPath condition assignment name context primitive handler functions fuel production source finalLocals final cost)
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
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,cost) ∧
    source.evaluateHOLFiniteState loop = (none,final) ∧
    ∃ (loweredFinal : PanSemStateFiniteExact 64 σ) (crepResult : Option (CrepResultHOLExact 64)) (crepFinal : CrepSemHOLState 64 σ),
      lowered.evaluateHOLFiniteState loweredLoop = (none,loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (none : Option (PanSemResultExact 64))) globals final loweredFinal ∧
      evalCrepSemHOLProgExact crep (compileProgExactHOLW ctxt loweredLoop) = (crepResult,crepFinal) ∧
      panToCrepStateRelFiniteExact loweredFinal crepFinal ∧
      pcCompileCorrectResultRel ctxt loweredFinal crepFinal none crepResult ∧
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW ctxt loweredLoop) crep ≤
        (1 + sizeOf (compileProgExactHOLW ctxt loweredBody)) * (1 + sizeOf loweredBody) * budget := by
  obtain ⟨exec,run,loweredFinal,loweredRun,finalRel,loweredBound⟩ :=
    assignLoopPath_global_steps condition assignment name context primitive handler functions path rel ranged budget budgetBound
      globals ctxt shape lowered globalRel
  obtain ⟨ce,crepResult,crepFinal,compiled,direct,branch,crepRun,crepRel,_,_,resultRel,crepBound⟩ :=
    while_correct_with_steps (compileExpExactHOL globals (expToHOL condition))
      (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))) ctxt
      (globalCompile_scalar_shape globals conditionShape) (globalCompile_branch_shape globals shape)
      lowered loweredFinal none crep (by simpa only [compileProgExactHOL] using loweredRun) (by simp)
      stateRel codeRel excpRel localsRel (by simpa only [compileProgExactHOL] using localised)
  refine ⟨exec,run,loweredFinal,crepResult,crepFinal,loweredRun,finalRel,?_,crepRel,resultRel,?_⟩
  · simpa only [compileProgExactHOL] using crepRun
  · have scaled := Nat.mul_le_mul_left
      (1 + sizeOf (compileProgExactHOLW ctxt (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))))) loweredBound
    simp only [compileProgExactHOL] at crepBound scaled ⊢
    simpa only [Nat.mul_assoc] using crepBound.trans scaled

end SteppedFlapjack.PanToCrepSteps
