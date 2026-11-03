module

public import SteppedFlapjack.PanValueExpCounted
@[expose] public section

/-!
Step-counted structured Pancake semantics.

The fuel argument of the existing evaluator in `PanValues` is a recursion
guard. It is deliberately not a cost: sequence evaluation restarts the guard
for its second component and loop evaluation restarts it for the next
iteration. This module keeps that evaluator intact and adds a parallel
statement evaluator whose successful result carries a compositional
source-step count.

The count is the number of source evaluation rules visited. Expressions are
evaluated and counted by `PanValueExpCounted` (one step per expression node,
plus its operands' steps). Every statement/control constructor costs one step,
while a call contributes one step for the call plus argument, callee, and any
resumed handler/continuation steps. `fuel` remains only the bound needed to
make the recursive definition executable.
-/

namespace Flapjack

abbrev PanValueSteppedResult (α : Type u) :=
  PanValueControlResult α × Nat
def PanTerminates (evaluate : Nat → Option α) : Prop :=
  ∃ fuel result, evaluate fuel = some result

def PanSteppedTerminates (evaluate : Nat → Option (α × Nat)) : Prop :=
  ∃ fuel result steps, evaluate fuel = some (result, steps)

def PanDiverges (evaluate : Nat → Option α) : Prop :=
  ¬ PanTerminates evaluate

def PanSteppedDiverges (evaluate : Nat → Option (α × Nat)) : Prop :=
  ¬ PanSteppedTerminates evaluate

theorem panSteppedTerminates_iff_of_projection_agrees
    (evaluate : Nat → Option α)
    (steppedEvaluate : Nat → Option (α × Nat))
    (hagree : ∀ fuel,
      (steppedEvaluate fuel).map Prod.fst = evaluate fuel) :
    PanSteppedTerminates steppedEvaluate ↔ PanTerminates evaluate := by
  constructor
  · rintro ⟨fuel, result, steps, hsteps⟩
    refine ⟨fuel, result, ?_⟩
    rw [← hagree fuel, hsteps]
    rfl
  · rintro ⟨fuel, result, horiginal⟩
    have hprojected : (steppedEvaluate fuel).map Prod.fst = some result := by
      rw [hagree fuel]
      exact horiginal
    cases hstepped : steppedEvaluate fuel with
    | none => simp [hstepped] at hprojected
    | some pair =>
        cases pair with
        | mk actual steps =>
            simp [hstepped] at hprojected
            cases hprojected
            exact ⟨fuel, result, steps, hstepped⟩

theorem panSteppedDiverges_iff_of_projection_agrees
    (evaluate : Nat → Option α)
    (steppedEvaluate : Nat → Option (α × Nat))
    (hagree : ∀ fuel,
      (steppedEvaluate fuel).map Prod.fst = evaluate fuel) :
    PanSteppedDiverges steppedEvaluate ↔ PanDiverges evaluate := by
  exact not_congr (panSteppedTerminates_iff_of_projection_agrees
    evaluate steppedEvaluate hagree)

mutual
  def evalPanValueCallWithPrimitiveCallsAndFfiSteps
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) →
        Option (PanValueSteppedResult α)
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments, memoryAccess, contracts,
        memoryHandler => do
        let (values, argumentSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord arguments memoryAccess
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← if panValueParametersValid structs contracts function values then
          bindPanValueParameters parameters values
        else none
        let (result, steps) ← evalPanValueProgWithPrimitiveCallsAndFfiSteps
          primitive handler structs functions baseAddress topAddress bytesInWord fuel
          calleeLocals globals memory body (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler)
        match result with
        | .normal _ _ _ => none
        | .returned _ calleeGlobals calleeMemory values =>
            -- HOL's Call checks only `shape_of retv <> return_sh`; the
            -- payload-size limit is enforced by the callee `Return`.
            if panValueReturnValid structs contracts function values then
              match info with
              | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory values,
                  argumentSteps + steps)
              | some (destination, _) => do
                  let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                    destination values
                    (structs := structs)
                  pure (.normal locals globals calleeMemory, argumentSteps + steps)
            else none
        | .raised _ calleeGlobals calleeMemory exception value =>
            if panValueExceptionValid structs contracts exception value &&
                panValuePayloadWithinLimit structs value then
              match info with
              | some (_, some (caught, handlerVariable, handlerProgram)) =>
                  if caught == exception then
                    if panValueHandlerValid structs contracts locals handlerVariable value then
                      let (result, handlerSteps) ←
                        evalPanValueProgWithPrimitiveCallsAndFfiSteps
                          primitive handler structs functions baseAddress topAddress bytesInWord fuel
                          (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory
                          handlerProgram (memoryAccess := memoryAccess) (contracts := contracts)
                          (memoryHandler := memoryHandler)
                      pure (result, argumentSteps + steps + handlerSteps)
                    else none
                  else pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value,
                    argumentSteps + steps)
              | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value,
                  argumentSteps + steps)
            else none
        | .broke _ _ _ | .continued _ _ _ => none
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithPrimitiveCallsAndFfiSteps
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        (program : Prog α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) →
        Option (PanValueSteppedResult α)
    | 0, _, _, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip, _, _, _ =>
        some (.normal locals globals memory, 1)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body, memoryAccess, contracts, memoryHandler => do
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let (result, steps) ← evalPanValueProgWithPrimitiveCallsAndFfiSteps
            primitive handler structs functions baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
            (memoryAccess := memoryAccess) (contracts := contracts)
            (memoryHandler := memoryHandler)
          pure (restorePanValueControlLocal name oldValue result, valueSteps + steps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value, memoryAccess,
        _contracts, _memoryHandler => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValueAssignmentValid structs locals globals .local name evaluatedValue then
          pure (.normal (updatePanValueMap locals name evaluatedValue) globals memory,
            valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .assign .global name value, memoryAccess,
        _contracts, _memoryHandler => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValueAssignmentValid structs locals globals .global name evaluatedValue then
          pure (.normal locals (updatePanValueMap globals name evaluatedValue) memory,
            valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments, memoryAccess,
        _contracts, _memoryHandler => do
        let (values, valueSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord arguments memoryAccess
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value)
            (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory, valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .store address value, memoryAccess,
        _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address memoryAccess
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        let .word address := address | none
        let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
        pure (.normal locals globals memory,
          addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory, .store32 address value, memoryAccess,
        _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address memoryAccess
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals memory, addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory, .storeByte address value, memoryAccess,
        _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address memoryAccess
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        pure (.normal locals globals memory, addressSteps + valueSteps + 1)
    | fuel + 1, locals, globals, memory, .seq first second, memoryAccess, contracts,
        memoryHandler => do
        let (firstResult, firstSteps) ←
          evalPanValueProgWithPrimitiveCallsAndFfiSteps
            primitive handler structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory first (memoryAccess := memoryAccess)
            (contracts := contracts) (memoryHandler := memoryHandler)
        match firstResult with
        | .normal locals globals memory =>
            let (secondResult, secondSteps) ←
              evalPanValueProgWithPrimitiveCallsAndFfiSteps
                primitive handler structs functions baseAddress topAddress bytesInWord fuel
                locals globals memory second (memoryAccess := memoryAccess)
                (contracts := contracts) (memoryHandler := memoryHandler)
            pure (secondResult, firstSteps + secondSteps + 1)
        | result => pure (result, firstSteps + 1)
    | _fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler => do
        let (condition, conditionSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord condition memoryAccess
        let .word condition := condition | none
        let (result, steps) ←
          if condition != 0 then
            evalPanValueProgWithPrimitiveCallsAndFfiSteps
              primitive handler structs functions baseAddress topAddress bytesInWord _fuel
              locals globals memory thenBranch (memoryAccess := memoryAccess)
              (contracts := contracts) (memoryHandler := memoryHandler)
          else
            evalPanValueProgWithPrimitiveCallsAndFfiSteps
              primitive handler structs functions baseAddress topAddress bytesInWord _fuel
              locals globals memory elseBranch (memoryAccess := memoryAccess)
              (contracts := contracts) (memoryHandler := memoryHandler)
        pure (result, conditionSteps + steps + 1)
    | fuel + 1, locals, globals, memory, .call info function arguments, memoryAccess, contracts,
        memoryHandler => do
        let (result, steps) ← evalPanValueCallWithPrimitiveCallsAndFfiSteps
          primitive handler structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory info function arguments (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler)
        pure (result, steps + 1)
    | fuel + 1, locals, globals, memory,
        .decCall name shape function arguments body, memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let (callResult, callSteps) ← evalPanValueCallWithPrimitiveCallsAndFfiSteps
          primitive handler structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory none function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match callResult with
        | .returned _ globals memory [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyResult, bodySteps) ←
                evalPanValueProgWithPrimitiveCallsAndFfiSteps
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  (updatePanValueMap locals name value) globals memory body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
              pure (restorePanValueControlLocal name oldValue bodyResult,
                callSteps + bodySteps + 1)
            else none
        | .raised _ globals memory exception value =>
            pure (.raised (fun _ => none) globals memory exception value,
              callSteps + 1)
        | _ => none
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength, memoryAccess,
        _contracts, memoryHandler => do
        let (values, expressionSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength] memoryAccess
        let [.word configuration, .word configurationLength, .word array, .word arrayLength] :=
          values | none
        match memoryHandler with
        | some memoryHandler =>
            let (locals, memory) ← memoryHandler function configuration configurationLength
              array arrayLength locals memory
            pure (.normal locals globals memory, expressionSteps + 1)
        | none =>
            let locals ← handler function configuration configurationLength array arrayLength locals
            pure (.normal locals globals memory, expressionSteps + 1)
    | fuel + 1, locals, globals, memory, .while conditionExp body, memoryAccess, contracts,
        memoryHandler => do
        let (condition, conditionSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp memoryAccess
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory, conditionSteps + 1)
        else
          let (bodyResult, bodySteps) ←
            evalPanValueProgWithPrimitiveCallsAndFfiSteps
              primitive handler structs functions baseAddress topAddress bytesInWord fuel
              locals globals memory body (memoryAccess := memoryAccess)
              (contracts := contracts) (memoryHandler := memoryHandler)
          match bodyResult with
          | .normal locals globals memory | .continued locals globals memory =>
              let (loopResult, loopSteps) ←
                evalPanValueProgWithPrimitiveCallsAndFfiSteps
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory (.while conditionExp body)
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
              pure (loopResult, conditionSteps + bodySteps + loopSteps + 1)
          | .broke locals globals memory =>
              pure (.normal locals globals memory, conditionSteps + bodySteps + 1)
          | result => pure (result, conditionSteps + bodySteps + 1)
    | _fuel + 1, locals, globals, memory, .break, _, _, _ =>
        pure (.broke locals globals memory, 1)
    | _fuel + 1, locals, globals, memory, .continue, _, _, _ =>
        pure (.continued locals globals memory, 1)
    | _fuel + 1, locals, globals, memory, .raise exception value, memoryAccess, contracts,
        _memoryHandler => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValueExceptionValid structs contracts exception evaluatedValue &&
            panValuePayloadWithinLimit structs evaluatedValue then
          pure (.raised (fun _ => none) globals memory exception evaluatedValue, valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .return value, memoryAccess, _contracts,
        _memoryHandler => do
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValuePayloadWithinLimit structs evaluatedValue then
          pure (.returned (fun _ => none) globals memory [evaluatedValue], valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory,
        .shMemLoad size kind name address, memoryAccess, _contracts, _memoryHandler => do
        let (evaluatedAddress, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address memoryAccess
        let .word evaluatedAddress := evaluatedAddress | none
        let value ← match memoryAccess with
          | none => memory evaluatedAddress
          | some access => access.sharedRead memory bytesInWord size evaluatedAddress
        if panValueSharedLoadValid structs locals globals kind name value then
          match kind with
          | .local => pure (.normal (updatePanValueMap locals name value) globals memory,
              addressSteps + 1)
          | .global => pure (.normal locals (updatePanValueMap globals name value) memory,
              addressSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, .shMemStore size address value, memoryAccess,
        _contracts, _memoryHandler => do
        let (evaluatedAddress, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address memoryAccess
        let (evaluatedValue, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        let .word evaluatedAddress := evaluatedAddress | none
        let .word evaluatedValue := evaluatedValue | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory evaluatedAddress (.word evaluatedValue))
          | some access =>
              access.sharedStore memory bytesInWord size evaluatedAddress
                (.word evaluatedValue)
        pure (.normal locals globals memory, addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory,
        .tick, _, _, _ | _fuel + 1, locals, globals, memory, .annot _ _, _, _, _ =>
        pure (.normal locals globals memory, 1)
    termination_by fuel _ _ _ _ => fuel
end

/-! Projection lemmas for composing a counted expression with a continuation.
These are the bind-level interface used by the eventual mutual evaluator
projection theorem: the continuation may inspect the source value and the
count, but its projected result must agree with the uncounted continuation. -/
theorem panOptionCountedBindMapFst
    {α : Type u} {β : Type v} (values : Option α) (steps : Nat)
    (stepped : α → Nat → Option (β × Nat))
    (original : α → Option β)
    (h : ∀ value step, (stepped value step).map Prod.fst = original value) :
    (values.map (fun value => (value, steps))).bind
        (fun pair => (stepped pair.1 pair.2).map Prod.fst) =
      values.bind original := by
  cases values with
  | none => rfl
  | some value => simp [h]

theorem panEvalPanValueExpCountedBindMapFst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expression : Exp α)
    (stepped : PanValue α → Nat → Option (β × Nat))
    (original : PanValue α → Option β)
    (h : ∀ value step, (stepped value step).map Prod.fst = original value) :
    (evalPanValueExpCounted structs locals globals memory baseAddress topAddress
        bytesInWord expression).bind
      (fun pair => (stepped pair.1 pair.2).map Prod.fst) =
      (evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord expression).bind original := by
  unfold evalPanValueExpCounted
  apply panOptionCountedBindMapFst
  exact h

theorem panEvalPanValueExpsCountedBindMapFst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expressions : List (Exp α))
    (stepped : List (PanValue α) → Nat → Option (β × Nat))
    (original : List (PanValue α) → Option β)
    (h : ∀ value step, (stepped value step).map Prod.fst = original value) :
    (evalPanValueExpsCounted structs locals globals memory baseAddress topAddress
        bytesInWord expressions).bind
      (fun pair => (stepped pair.1 pair.2).map Prod.fst) =
      (evalPanValueExps structs locals globals memory baseAddress topAddress
        bytesInWord expressions).bind original := by
  unfold evalPanValueExpsCounted
  apply panOptionCountedBindMapFst
  exact h

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_assign_local
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (name : VarName) (value : Exp α) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.assign .local name value)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.assign .local name value) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases hvalue : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord value with
  | none => simp [hvalue, evalPanValueExpCounted]
  | some evaluatedValue => simp [hvalue, evalPanValueExpCounted]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_assign_global
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (name : VarName) (value : Exp α) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.assign .global name value)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.assign .global name value) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases hvalue : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord value with
  | none => simp [hvalue, evalPanValueExpCounted]
  | some evaluatedValue => simp [hvalue, evalPanValueExpCounted]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_primitive
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (name : VarName)
    (operator : PrimOp) (arguments : List (Exp α)) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.primitive name operator arguments)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.primitive name operator arguments) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments with
  | none => simp [hargs, evalPanValueExpsCounted]
  | some values =>
      cases hprimitive : primitive operator values with
      | none => simp [hargs, hprimitive, evalPanValueExpsCounted]
      | some value =>
          cases hold : locals name with
          | none => simp [hargs, evalPanValueExpsCounted]
          | some oldValue =>
              simp [hargs, hprimitive, evalPanValueExpsCounted]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_store
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (address value : Exp α) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.store address value)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.store address value) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases haddress : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord address with
  | none => simp [haddress, evalPanValueExpCounted]
  | some evaluatedAddress =>
      cases hvalue : evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value with
      | none => simp [haddress, hvalue, evalPanValueExpCounted, panValueStoreWithAccess]
      | some evaluatedValue =>
          cases evaluatedAddress <;>
            simp [haddress, hvalue, evalPanValueExpCounted, panValueStoreWithAccess,
              Function.comp_def]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .skip).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .skip := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_break
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .break).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .break := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_continue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .continue).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .continue := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_tick
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .tick).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory .tick := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_annot
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (tag text : String) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.annot tag text)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.annot tag text) := by
  simp [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_raise
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (exception : ExceptionId) (value : Exp α) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.raise exception value)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.raise exception value) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases hvalue : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord value with
  | none => simp [hvalue, evalPanValueExpCounted]
  | some evaluatedValue => simp [hvalue, evalPanValueExpCounted]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_return
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (value : Exp α) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.return value)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.return value) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases hvalue : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord value with
  | none => simp [hvalue, evalPanValueExpCounted]
  | some evaluatedValue => simp [hvalue, evalPanValueExpCounted]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_store32
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (address value : Exp α) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.store32 address value)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.store32 address value) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases haddress : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord address with
  | none => simp [haddress, evalPanValueExpCounted]
  | some evaluatedAddress =>
      cases hvalue : evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value with
      | none => simp [haddress, hvalue, evalPanValueExpCounted]
      | some evaluatedValue =>
          cases evaluatedAddress <;> cases evaluatedValue <;>
            simp [haddress, hvalue, evalPanValueExpCounted]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_storeByte
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (address value : Exp α) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.storeByte address value)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory (.storeByte address value) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases haddress : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord address with
  | none => simp [haddress, evalPanValueExpCounted]
  | some evaluatedAddress =>
      cases hvalue : evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value with
      | none => simp [haddress, hvalue, evalPanValueExpCounted]
      | some evaluatedValue =>
          cases evaluatedAddress <;> cases evaluatedValue <;>
            simp [haddress, hvalue, evalPanValueExpCounted]

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_seq_of_projections
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (first second : Prog α)
    (hfirst :
      (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory first).map Prod.fst =
        evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory first)
    (hsecond : ∀ locals globals memory,
      (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory second).map Prod.fst =
        evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory second) :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.seq first second)).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory
      (.seq first second) := by
  simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
    evalPanValueProgWithPrimitiveCallsAndFfi]
  cases hstep : evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler
      structs functions baseAddress topAddress bytesInWord fuel locals globals memory first with
  | none =>
      have horiginal :
          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
            baseAddress topAddress bytesInWord fuel locals globals memory first = none := by
        rw [← hfirst]
        simp [hstep]
      simp [horiginal]
  | some pair =>
      cases pair with
      | mk result firstSteps =>
          have horiginal :
              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
                baseAddress topAddress bytesInWord fuel locals globals memory first =
                some result := by
            rw [← hfirst]
            simp [hstep]
          cases result with
          | normal firstLocals firstGlobals firstMemory =>
              cases hsecondStep : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  firstLocals firstGlobals firstMemory second with
              | none =>
                  have hsecondOriginal :
                      evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
                        baseAddress topAddress bytesInWord fuel firstLocals firstGlobals
                        firstMemory second = none := by
                    rw [← hsecond firstLocals firstGlobals firstMemory]
                    simp [hsecondStep]
                  simp [hsecondStep, horiginal, hsecondOriginal]
              | some secondPair =>
                  cases secondPair with
                  | mk secondResult secondSteps =>
                      have hsecondOriginal :
                          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                            functions baseAddress topAddress bytesInWord fuel firstLocals
                            firstGlobals firstMemory second = some secondResult := by
                        rw [← hsecond firstLocals firstGlobals firstMemory]
                        simp [hsecondStep]
                      simp [hsecondStep, horiginal, hsecondOriginal]
          | returned _ _ _ _ | raised _ _ _ _ _ | broke _ _ _ | continued _ _ _ =>
              simp [horiginal]

theorem evalPanValueCallWithPrimitiveCallsAndFfiSteps_fst_of_projection
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (hprogram : ∀ fuel (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (program : Prog α),
      (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory program).map Prod.fst =
      evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory program) :
    (evalPanValueCallWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory info function arguments).map
        Prod.fst =
    evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory info function arguments := by
  cases fuel with
  | zero => simp [evalPanValueCallWithPrimitiveCallsAndFfiSteps,
      evalPanValueCallWithPrimitiveCallsAndFfi]
  | succ fuel =>
      simp only [evalPanValueCallWithPrimitiveCallsAndFfiSteps,
        evalPanValueCallWithPrimitiveCallsAndFfi]
      cases hargs : evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments with
      | none => simp [hargs, evalPanValueExpsCounted]
      | some values =>
          simp [hargs, evalPanValueExpsCounted]
          cases hlookup : lookupPanFunction function functions with
          | none => simp
          | some callee =>
              cases hparams : bindPanValueParameters callee.1 values with
              | none => simp [hparams]
              | some calleeLocals =>
                  cases hstep : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                      primitive handler structs functions baseAddress topAddress bytesInWord fuel
                      calleeLocals globals memory callee.2 with
                  | none =>
                      have horiginal :
                          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                            functions baseAddress topAddress bytesInWord fuel calleeLocals globals
                            memory callee.2 = none := by
                        rw [← hprogram fuel calleeLocals globals memory callee.2]
                        simp [hstep]
                      simp [hparams, hstep, horiginal]
                  | some pair =>
                      cases pair with
                      | mk result steps =>
                          have horiginal :
                              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                functions baseAddress topAddress bytesInWord fuel calleeLocals
                                globals memory callee.2 = some result := by
                            rw [← hprogram fuel calleeLocals globals memory callee.2]
                            simp [hstep]
                          cases result with
                          | normal _ _ _ =>
                              simp [hparams, hstep, horiginal]
                          | returned _ calleeGlobals calleeMemory values =>
                              cases info with
                              | none => simp [hparams, hstep, horiginal]
                              | some info =>
                                  cases hassign : assignPanValueCallResult locals calleeGlobals info.1 values
                                    (structs := structs) with
                                  | none => simp [hparams, hstep, horiginal, hassign]
                                  | some assignedLocals =>
                                      simp [hparams, hstep, horiginal, hassign]
                          | raised _ calleeGlobals calleeMemory exception value =>
                              cases info with
                              | none => simp [hparams, hstep, horiginal]
                              | some info =>
                                  cases info with
                                  | mk destination handlerOption =>
                                      cases handlerOption with
                                      | none => simp [hparams, hstep, horiginal]
                                      | some handlerInfo =>
                                          cases handlerInfo with
                                          | mk caught handlerInfo =>
                                              cases handlerInfo with
                                              | mk handlerVariable handlerProgram =>
                                              by_cases heq : caught == exception
                                              · cases hhandler :
                                                    evalPanValueProgWithPrimitiveCallsAndFfiSteps
                                                      primitive handler structs functions
                                                      baseAddress topAddress bytesInWord fuel
                                                      (updatePanValueMap locals handlerVariable value)
                                                      calleeGlobals calleeMemory handlerProgram with
                                                | none =>
                                                    have hhandlerOriginal :
                                                        evalPanValueProgWithPrimitiveCallsAndFfi
                                                          primitive handler structs functions
                                                          baseAddress topAddress bytesInWord fuel
                                                          (updatePanValueMap locals handlerVariable value)
                                                          calleeGlobals calleeMemory handlerProgram = none := by
                                                      rw [← hprogram fuel
                                                        (updatePanValueMap locals handlerVariable value)
                                                        calleeGlobals calleeMemory handlerProgram]
                                                      simp [hhandler]
                                                    have heqeq : caught = exception := by
                                                      simpa using heq
                                                    simp [hparams, hstep, horiginal, heqeq, hhandler,
                                                      hhandlerOriginal]
                                                | some handlerPair =>
                                                    cases handlerPair with
                                                    | mk handlerResult handlerSteps =>
                                                        have hhandlerOriginal :
                                                            evalPanValueProgWithPrimitiveCallsAndFfi
                                                              primitive handler structs functions
                                                              baseAddress topAddress bytesInWord fuel
                                                              (updatePanValueMap locals handlerVariable value)
                                                              calleeGlobals calleeMemory handlerProgram =
                                                              some handlerResult := by
                                                          rw [← hprogram fuel
                                                            (updatePanValueMap locals handlerVariable value)
                                                            calleeGlobals calleeMemory handlerProgram]
                                                          simp [hhandler]
                                                        have heqeq : caught = exception := by
                                                          simpa using heq
                                                        simp [hparams, hstep, horiginal, heqeq, hhandler,
                                                          hhandlerOriginal]
                                              · have hneq : caught ≠ exception := by
                                                  intro equality
                                                  apply heq
                                                  simp [equality]
                                                simp [hparams, hstep, horiginal, hneq]
                          | broke _ _ _ | continued _ _ _ =>
                              simp [hparams, hstep, horiginal]

theorem evalPanValueCallAndProgWithPrimitiveCallsAndFfiSteps_fst :
    ∀ [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) (fuel : Nat)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (info : Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)))
      (function : FunName) (arguments : List (Exp α)),
      (evalPanValueCallWithPrimitiveCallsAndFfiSteps primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory info function arguments).map
          Prod.fst =
        evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory info function arguments ∧
      ∀ program,
        (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory program).map Prod.fst =
        evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory program := by
  intro instBEq instOfNat0 instOfNat1 instAdd instMul instSub instAndOp instOrOp instHXor
    instShiftLeft instShiftRight instLT instDecidable instPanCmp primitive handler structs functions
    baseAddress topAddress bytesInWord fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro locals globals memory info function arguments
      constructor
      · cases fuel with
        | zero =>
            simp [evalPanValueCallWithPrimitiveCallsAndFfiSteps,
              evalPanValueCallWithPrimitiveCallsAndFfi]
        | succ fuel =>
            simp only [evalPanValueCallWithPrimitiveCallsAndFfiSteps,
              evalPanValueCallWithPrimitiveCallsAndFfi]
            cases hargs : evalPanValueExps structs locals globals memory
                baseAddress topAddress bytesInWord arguments with
            | none => simp [hargs, evalPanValueExpsCounted]
            | some values =>
                simp [hargs, evalPanValueExpsCounted]
                cases hlookup : lookupPanFunction function functions with
                | none => simp
                | some callee =>
                    cases hparams : bindPanValueParameters callee.1 values with
                    | none => simp [hparams]
                    | some calleeLocals =>
                        cases hstep : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                            primitive handler structs functions baseAddress topAddress bytesInWord fuel
                            calleeLocals globals memory callee.2 with
                        | none =>
                            have horiginal :
                                evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                  functions baseAddress topAddress bytesInWord fuel calleeLocals globals
                                  memory callee.2 = none := by
                              rw [← (ih fuel (Nat.lt_succ_self fuel) calleeLocals globals memory
                                none function arguments).2 callee.2]
                              simp [hstep]
                            simp [hparams, hstep, horiginal]
                        | some pair =>
                            cases pair with
                            | mk result steps =>
                                have horiginal :
                                    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                      functions baseAddress topAddress bytesInWord fuel calleeLocals
                                      globals memory callee.2 = some result := by
                                  rw [← (ih fuel (Nat.lt_succ_self fuel) calleeLocals globals memory
                                    none function arguments).2 callee.2]
                                  simp [hstep]
                                cases result with
                                | normal _ _ _ =>
                                    simp [hparams, hstep, horiginal]
                                | returned _ calleeGlobals calleeMemory values =>
                                    cases info with
                                    | none => simp [hparams, hstep, horiginal]
                                    | some info =>
                                        cases hassign : assignPanValueCallResult locals calleeGlobals info.1 values
                                          (structs := structs) with
                                        | none => simp [hparams, hstep, horiginal, hassign]
                                        | some assignedLocals =>
                                            simp [hparams, hstep, horiginal, hassign]
                                | raised _ calleeGlobals calleeMemory exception value =>
                                    cases info with
                                    | none => simp [hparams, hstep, horiginal]
                                    | some info =>
                                        cases info with
                                        | mk destination handlerOption =>
                                            cases handlerOption with
                                            | none => simp [hparams, hstep, horiginal]
                                            | some handlerInfo =>
                                                cases handlerInfo with
                                                | mk caught handlerInfo =>
                                                    cases handlerInfo with
                                                    | mk handlerVariable handlerProgram =>
                                                        by_cases heq : caught == exception
                                                        · cases hhandler :
                                                              evalPanValueProgWithPrimitiveCallsAndFfiSteps
                                                                primitive handler structs functions
                                                                baseAddress topAddress bytesInWord fuel
                                                                (updatePanValueMap locals handlerVariable value)
                                                                calleeGlobals calleeMemory handlerProgram with
                                                          | none =>
                                                              have hhandlerOriginal :
                                                                  evalPanValueProgWithPrimitiveCallsAndFfi
                                                                    primitive handler structs functions
                                                                    baseAddress topAddress bytesInWord fuel
                                                                    (updatePanValueMap locals handlerVariable value)
                                                                    calleeGlobals calleeMemory handlerProgram = none := by
                                                                rw [← (ih fuel (Nat.lt_succ_self fuel)
                                                                  (updatePanValueMap locals handlerVariable value)
                                                                  calleeGlobals calleeMemory none function arguments).2 handlerProgram]
                                                                simp [hhandler]
                                                              have heqeq : caught = exception := by
                                                                simpa using heq
                                                              simp [hparams, hstep, horiginal, heqeq, hhandler,
                                                                hhandlerOriginal]
                                                          | some handlerPair =>
                                                              cases handlerPair with
                                                              | mk handlerResult handlerSteps =>
                                                                  have hhandlerOriginal :
                                                                      evalPanValueProgWithPrimitiveCallsAndFfi
                                                                        primitive handler structs functions
                                                                        baseAddress topAddress bytesInWord fuel
                                                                        (updatePanValueMap locals handlerVariable value)
                                                                        calleeGlobals calleeMemory handlerProgram =
                                                                        some handlerResult := by
                                                                    rw [← (ih fuel (Nat.lt_succ_self fuel)
                                                                      (updatePanValueMap locals handlerVariable value)
                                                                      calleeGlobals calleeMemory none function arguments).2 handlerProgram]
                                                                    simp [hhandler]
                                                                  have heqeq : caught = exception := by
                                                                    simpa using heq
                                                                  simp [hparams, hstep, horiginal, heqeq, hhandler,
                                                                    hhandlerOriginal]
                                                        · have hneq : caught ≠ exception := by
                                                            intro equality
                                                            apply heq
                                                            simp [equality]
                                                          simp [hparams, hstep, horiginal, hneq]
                                | broke _ _ _ | continued _ _ _ =>
                                    simp [hparams, hstep, horiginal]
      · intro program
        cases fuel with
        | zero =>
            simp [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
              evalPanValueProgWithPrimitiveCallsAndFfi]
        | succ fuel =>
            cases program with
            | skip =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_skip
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory
            | dec name shape value body =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases hvalue : evalPanValueExp structs locals globals memory
                    baseAddress topAddress bytesInWord value with
                | none => simp [hvalue, evalPanValueExpCounted]
                | some evaluatedValue =>
                    by_cases hshape : panShapeMatches (panValueShape structs evaluatedValue) shape
                    · cases hbody : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                          primitive handler structs functions baseAddress topAddress bytesInWord fuel
                          (updatePanValueMap locals name evaluatedValue) globals memory body with
                      | none =>
                          have hbodyOriginal :
                              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                functions baseAddress topAddress bytesInWord fuel
                                (updatePanValueMap locals name evaluatedValue) globals memory body = none := by
                            rw [← (ih fuel (Nat.lt_succ_self fuel)
                              (updatePanValueMap locals name evaluatedValue) globals memory
                              none function arguments).2 body]
                            simp [hbody]
                          simp [hvalue, hshape, hbody, hbodyOriginal, evalPanValueExpCounted]
                      | some bodyPair =>
                          cases bodyPair with
                          | mk bodyResult bodySteps =>
                              have hbodyOriginal :
                                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                    functions baseAddress topAddress bytesInWord fuel
                                    (updatePanValueMap locals name evaluatedValue) globals memory body =
                                    some bodyResult := by
                                rw [← (ih fuel (Nat.lt_succ_self fuel)
                                  (updatePanValueMap locals name evaluatedValue) globals memory
                                  none function arguments).2 body]
                                simp [hbody]
                              simp [hvalue, hshape, hbody, hbodyOriginal, evalPanValueExpCounted]
                    · simp [hvalue, hshape, evalPanValueExpCounted]
            | assign kind name value =>
                cases kind
                · exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_assign_local
                    primitive handler structs functions baseAddress topAddress bytesInWord fuel
                    locals globals memory name value
                · exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_assign_global
                    primitive handler structs functions baseAddress topAddress bytesInWord fuel
                    locals globals memory name value
            | primitive name operator arguments =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_primitive
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory name operator arguments
            | store address value =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_store
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory address value
            | store32 address value =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_store32
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory address value
            | storeByte address value =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_storeByte
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory address value
            | seq first second =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_seq_of_projections
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory first second
                  ((ih fuel (Nat.lt_succ_self fuel) locals globals memory
                    none function arguments).2 first)
                  (fun nextLocals nextGlobals nextMemory =>
                    (ih fuel (Nat.lt_succ_self fuel) nextLocals nextGlobals nextMemory
                      none function arguments).2 second)
            | ite condition thenBranch elseBranch =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases hcondition : evalPanValueExp structs locals globals memory
                    baseAddress topAddress bytesInWord condition with
                | none => simp [hcondition, evalPanValueExpCounted]
                | some evaluatedCondition =>
                    cases evaluatedCondition with
                    | word conditionValue =>
                        by_cases hselected : conditionValue != 0
                        · cases hbranch : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                              primitive handler structs functions baseAddress topAddress bytesInWord fuel
                              locals globals memory thenBranch with
                          | none =>
                              have hbranchOriginal :
                                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                    functions baseAddress topAddress bytesInWord fuel locals globals
                                    memory thenBranch = none := by
                                rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                                  none function arguments).2 thenBranch]
                                simp [hbranch]
                              simp [hcondition, hselected, hbranchOriginal,
                                evalPanValueExpCounted]
                          | some branchPair =>
                              cases branchPair with
                              | mk branchResult branchSteps =>
                                  have hbranchOriginal :
                                      evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                        functions baseAddress topAddress bytesInWord fuel locals globals
                                        memory thenBranch = some branchResult := by
                                    rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                                      none function arguments).2 thenBranch]
                                    simp [hbranch]
                                  simp [hcondition, hselected, hbranchOriginal,
                                    evalPanValueExpCounted]
                        · cases hbranch : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                              primitive handler structs functions baseAddress topAddress bytesInWord fuel
                              locals globals memory elseBranch with
                          | none =>
                              have hbranchOriginal :
                                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                    functions baseAddress topAddress bytesInWord fuel locals globals
                                    memory elseBranch = none := by
                                rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                                  none function arguments).2 elseBranch]
                                simp [hbranch]
                              simp [hcondition, hselected, hbranchOriginal,
                                evalPanValueExpCounted]
                          | some branchPair =>
                              cases branchPair with
                              | mk branchResult branchSteps =>
                                  have hbranchOriginal :
                                      evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                        functions baseAddress topAddress bytesInWord fuel locals globals
                                        memory elseBranch = some branchResult := by
                                    rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                                      none function arguments).2 elseBranch]
                                    simp [hbranch]
                                  simp [hcondition, hselected, hbranchOriginal,
                                    evalPanValueExpCounted]
                    | rStruct _ | nStruct _ _ =>
                        simp [hcondition, evalPanValueExpCounted]
            | «while» condition body =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases hcondition : evalPanValueExp structs locals globals memory
                    baseAddress topAddress bytesInWord condition with
                | none => simp [hcondition, evalPanValueExpCounted]
                | some evaluatedCondition =>
                    cases evaluatedCondition with
                    | rStruct _ | nStruct _ _ =>
                        simp [hcondition, evalPanValueExpCounted]
                    | word conditionValue =>
                        by_cases hzero : conditionValue == 0
                        · simp [hcondition, hzero, evalPanValueExpCounted]
                        · cases hbody : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                              primitive handler structs functions baseAddress topAddress bytesInWord fuel
                              locals globals memory body with
                          | none =>
                              have hbodyOriginal :
                                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                    functions baseAddress topAddress bytesInWord fuel locals globals
                                    memory body = none := by
                                rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                                  none function arguments).2 body]
                                simp [hbody]
                              simp [hcondition, hzero, hbodyOriginal,
                                evalPanValueExpCounted]
                          | some bodyPair =>
                              cases bodyPair with
                              | mk bodyResult bodySteps =>
                                  have hbodyOriginal :
                                      evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                        functions baseAddress topAddress bytesInWord fuel locals globals
                                        memory body = some bodyResult := by
                                    rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                                      none function arguments).2 body]
                                    simp [hbody]
                                  cases bodyResult with
                                  | normal bodyLocals bodyGlobals bodyMemory =>
                                      cases hloop : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                                          primitive handler structs functions baseAddress topAddress bytesInWord fuel
                                          bodyLocals bodyGlobals bodyMemory (.while condition body) with
                                      | none =>
                                          have hloopOriginal :
                                              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                                functions baseAddress topAddress bytesInWord fuel bodyLocals
                                                bodyGlobals bodyMemory (.while condition body) = none := by
                                            rw [← (ih fuel (Nat.lt_succ_self fuel) bodyLocals bodyGlobals
                                              bodyMemory none function arguments).2 (.while condition body)]
                                            simp [hloop]
                                          simp [hcondition, hzero, hbodyOriginal, hloop,
                                            hloopOriginal, evalPanValueExpCounted]
                                      | some loopPair =>
                                          cases loopPair with
                                          | mk loopResult loopSteps =>
                                              have hloopOriginal :
                                                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                                                    structs functions baseAddress topAddress bytesInWord fuel
                                                    bodyLocals bodyGlobals bodyMemory (.while condition body) =
                                                    some loopResult := by
                                                rw [← (ih fuel (Nat.lt_succ_self fuel) bodyLocals
                                                  bodyGlobals bodyMemory none function arguments).2
                                                  (.while condition body)]
                                                simp [hloop]
                                              simp [hcondition, hzero, hbodyOriginal, hloop,
                                                hloopOriginal, evalPanValueExpCounted]
                                  | continued bodyLocals bodyGlobals bodyMemory =>
                                      cases hloop : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                                          primitive handler structs functions baseAddress topAddress bytesInWord fuel
                                          bodyLocals bodyGlobals bodyMemory (.while condition body) with
                                      | none =>
                                          have hloopOriginal :
                                              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs
                                                functions baseAddress topAddress bytesInWord fuel bodyLocals
                                                bodyGlobals bodyMemory (.while condition body) = none := by
                                            rw [← (ih fuel (Nat.lt_succ_self fuel) bodyLocals bodyGlobals
                                              bodyMemory none function arguments).2 (.while condition body)]
                                            simp [hloop]
                                          simp [hcondition, hzero, hbodyOriginal, hloop,
                                            hloopOriginal, evalPanValueExpCounted]
                                      | some loopPair =>
                                          cases loopPair with
                                          | mk loopResult loopSteps =>
                                              have hloopOriginal :
                                                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                                                    structs functions baseAddress topAddress bytesInWord fuel
                                                    bodyLocals bodyGlobals bodyMemory (.while condition body) =
                                                    some loopResult := by
                                                rw [← (ih fuel (Nat.lt_succ_self fuel) bodyLocals
                                                  bodyGlobals bodyMemory none function arguments).2
                                                  (.while condition body)]
                                                simp [hloop]
                                              simp [hcondition, hzero, hbodyOriginal, hloop,
                                                hloopOriginal, evalPanValueExpCounted]
                                  | broke bodyLocals bodyGlobals bodyMemory =>
                                      simp [hcondition, hzero, hbodyOriginal,
                                        evalPanValueExpCounted]
                                  | returned _ _ _ _ | raised _ _ _ _ _ =>
                                      simp [hcondition, hzero, hbodyOriginal,
                                        evalPanValueExpCounted]
            | «break» =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_break
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory
            | «continue» =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_continue
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory
            | call info function arguments =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases hcall : evalPanValueCallWithPrimitiveCallsAndFfiSteps
                    primitive handler structs functions baseAddress topAddress bytesInWord fuel
                    locals globals memory info function arguments with
                | none =>
                    have hcallOriginal :
                        evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
                          functions baseAddress topAddress bytesInWord fuel locals globals memory
                          info function arguments = none := by
                      rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                        info function arguments).1]
                      simp [hcall]
                    simp [hcallOriginal]
                | some callPair =>
                    cases callPair with
                    | mk callResult callSteps =>
                        have hcallOriginal :
                            evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
                              functions baseAddress topAddress bytesInWord fuel locals globals memory
                              info function arguments = some callResult := by
                          rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                            info function arguments).1]
                          simp [hcall]
                        simp [hcallOriginal]
            | decCall name shape function arguments body =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases hcall : evalPanValueCallWithPrimitiveCallsAndFfiSteps
                    primitive handler structs functions baseAddress topAddress bytesInWord fuel
                    locals globals memory none function arguments with
                | none =>
                    have hcallOriginal :
                        evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
                          functions baseAddress topAddress bytesInWord fuel locals globals memory
                          none function arguments = none := by
                      rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                        none function arguments).1]
                      simp [hcall]
                    simp [hcallOriginal]
                | some callPair =>
                    cases callPair with
                    | mk callResult callSteps =>
                        have hcallOriginal :
                            evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
                              functions baseAddress topAddress bytesInWord fuel locals globals memory
                              none function arguments =
                              some callResult := by
                          rw [← (ih fuel (Nat.lt_succ_self fuel) locals globals memory
                            none function arguments).1]
                          simp [hcall]
                        cases callResult with
                        | returned callLocals callGlobals callMemory values =>
                            cases values with
                            | nil => simp [hcallOriginal]
                            | cons value rest =>
                                cases rest with
                                | nil =>
                                    by_cases hshape :
                                        panShapeMatches (panValueShape structs value) shape
                                    · cases hbody : evalPanValueProgWithPrimitiveCallsAndFfiSteps
                                          primitive handler structs functions baseAddress topAddress
                                          bytesInWord fuel (updatePanValueMap locals name value)
                                          callGlobals callMemory body with
                                      | none =>
                                          have hbodyOriginal :
                                              evalPanValueProgWithPrimitiveCallsAndFfi primitive
                                                handler structs functions baseAddress topAddress
                                                bytesInWord fuel
                                                (updatePanValueMap locals name value)
                                                callGlobals callMemory body = none := by
                                            rw [← (ih fuel (Nat.lt_succ_self fuel)
                                              (updatePanValueMap locals name value)
                                              callGlobals callMemory none function arguments).2 body]
                                            simp [hbody]
                                          simp [hcallOriginal, hshape, hbody, hbodyOriginal]
                                      | some bodyPair =>
                                          cases bodyPair with
                                          | mk bodyResult bodySteps =>
                                              have hbodyOriginal :
                                                  evalPanValueProgWithPrimitiveCallsAndFfi
                                                    primitive handler structs functions
                                                    baseAddress topAddress bytesInWord fuel
                                                    (updatePanValueMap locals name value)
                                                    callGlobals callMemory body = some bodyResult := by
                                                rw [← (ih fuel (Nat.lt_succ_self fuel)
                                                  (updatePanValueMap locals name value)
                                                  callGlobals callMemory none function arguments).2 body]
                                                simp [hbody]
                                              simp [hcallOriginal, hshape, hbody, hbodyOriginal]
                                    · simp [hcallOriginal, hshape]
                                | cons _ _ => simp [hcallOriginal]
                        | normal _ _ _ | raised _ _ _ _ _ | broke _ _ _ | continued _ _ _ =>
                            simp [hcallOriginal]
            | extCall function configuration configurationLength array arrayLength =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases hconfiguration : evalPanValueExp structs locals globals memory
                    baseAddress topAddress bytesInWord configuration with
                | none => simp [hconfiguration, evalPanValueExps, evalPanValueExp.evalPanValueExps,
                    evalPanValueExpsCounted,
                    ]
                | some evaluatedConfiguration =>
                    cases hconfigurationLength : evalPanValueExp structs locals globals memory
                        baseAddress topAddress bytesInWord configurationLength with
                    | none => simp [hconfiguration, hconfigurationLength, evalPanValueExps,
                        evalPanValueExp.evalPanValueExps,
                        evalPanValueExpsCounted]
                    | some evaluatedConfigurationLength =>
                        cases harray : evalPanValueExp structs locals globals memory
                            baseAddress topAddress bytesInWord array with
                        | none => simp [hconfiguration, hconfigurationLength, harray,
                            evalPanValueExps, evalPanValueExp.evalPanValueExps,
                            evalPanValueExpsCounted]
                        | some evaluatedArray =>
                            cases harrayLength : evalPanValueExp structs locals globals memory
                                baseAddress topAddress bytesInWord arrayLength with
                            | none => simp [hconfiguration, hconfigurationLength, harray,
                                harrayLength, evalPanValueExps, evalPanValueExp.evalPanValueExps,
                                evalPanValueExpsCounted,
                                ]
                            | some evaluatedArrayLength =>
                                cases evaluatedConfiguration with
                                | word configurationValue =>
                                    cases evaluatedConfigurationLength with
                                    | word configurationLengthValue =>
                                        cases evaluatedArray with
                                        | word arrayValue =>
                                            cases evaluatedArrayLength with
                                            | word arrayLengthValue =>
                                                cases hhandlerResult : handler function
                                                    configurationValue configurationLengthValue arrayValue
                                                    arrayLengthValue locals with
                                                | none =>
                                                    simp [hconfiguration, hconfigurationLength, harray,
                                                      harrayLength, hhandlerResult, evalPanValueExps,
                                                      evalPanValueExp.evalPanValueExps,
                                                      evalPanValueExpsCounted]
                                                | some newLocals =>
                                                    simp [hconfiguration, hconfigurationLength, harray,
                                                      harrayLength, hhandlerResult, evalPanValueExps,
                                                      evalPanValueExp.evalPanValueExps,
                                                      evalPanValueExpsCounted]
                                            | rStruct _ | nStruct _ _ =>
                                                simp [hconfiguration, hconfigurationLength, harray,
                                                  harrayLength, evalPanValueExps,
                                                  evalPanValueExp.evalPanValueExps,
                                                  evalPanValueExpsCounted]
                                        | rStruct _ | nStruct _ _ =>
                                            simp [hconfiguration, hconfigurationLength, harray,
                                              harrayLength, evalPanValueExps,
                                              evalPanValueExp.evalPanValueExps,
                                              evalPanValueExpsCounted]
                                    | rStruct _ | nStruct _ _ =>
                                        simp [hconfiguration, hconfigurationLength, harray,
                                          harrayLength, evalPanValueExps,
                                          evalPanValueExp.evalPanValueExps,
                                          evalPanValueExpsCounted]
                                | rStruct _ | nStruct _ _ =>
                                    simp [hconfiguration, hconfigurationLength, harray,
                                      harrayLength, evalPanValueExps,
                                      evalPanValueExp.evalPanValueExps,
                                      evalPanValueExpsCounted]
            | raise exception value =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_raise
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory exception value
            | «return» value =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_return
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory value
            | shMemLoad size kind name address =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases haddress : evalPanValueExp structs locals globals memory
                    baseAddress topAddress bytesInWord address with
                | none => simp [haddress, evalPanValueExpCounted]
                | some evaluatedAddress =>
                    cases evaluatedAddress with
                    | word evaluatedAddress =>
                        cases hmemory : memory evaluatedAddress with
                        | none => simp [haddress, hmemory, evalPanValueExpCounted]
                        | some evaluatedValue =>
                            cases evaluatedValue with
                            | word evaluatedValue =>
                                by_cases hvalid : panValueSharedLoadValid structs locals globals kind name
                                    (.word evaluatedValue)
                                · simp [haddress, hmemory, hvalid, evalPanValueExpCounted] <;>
                                    cases kind <;> rfl
                                · simp [haddress, hmemory, hvalid, evalPanValueExpCounted] <;>
                                    cases kind <;> rfl
                            | rStruct _ | nStruct _ _ =>
                                simp [haddress, hmemory, evalPanValueExpCounted,
                                  panValueSharedLoadValid]
                    | rStruct _ | nStruct _ _ =>
                        simp [haddress, evalPanValueExpCounted]
            | shMemStore size address value =>
                simp only [evalPanValueProgWithPrimitiveCallsAndFfiSteps,
                  evalPanValueProgWithPrimitiveCallsAndFfi]
                cases haddress : evalPanValueExp structs locals globals memory
                    baseAddress topAddress bytesInWord address with
                | none => simp [haddress, evalPanValueExpCounted]
                | some evaluatedAddress =>
                    cases hvalue : evalPanValueExp structs locals globals memory
                        baseAddress topAddress bytesInWord value with
                    | none => simp [haddress, hvalue, evalPanValueExpCounted]
                    | some evaluatedValue =>
                        cases evaluatedAddress <;>
                          cases evaluatedValue <;>
                          cases size <;>
                          simp [haddress, hvalue, evalPanValueExpCounted]
            | tick =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_tick
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory
            | annot tag text =>
                exact evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst_annot
                  primitive handler structs functions baseAddress topAddress bytesInWord fuel
                  locals globals memory tag text

theorem evalPanValueCallWithPrimitiveCallsAndFfiSteps_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) :
    (evalPanValueCallWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory info function arguments).map
        Prod.fst =
    evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory info function arguments :=
  (evalPanValueCallAndProgWithPrimitiveCallsAndFfiSteps_fst primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory info function arguments).1

theorem evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (program : Prog α) :
  (evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory program).map Prod.fst =
    evalPanValueProgWithPrimitiveCallsAndFfi primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory program :=
  (evalPanValueCallAndProgWithPrimitiveCallsAndFfiSteps_fst primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory none "" []).2 program

def evalPanValueSteppedProg
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) :
    Option (PanValueSteppedResult α) :=
  evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory program
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)

def evalPanValueSteppedProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) :
    Option (PanValueSteppedResult α) := do
  let state ← evalPanValueDeclarations initial declarations
  let result ← evalPanValueProgWithPrimitiveCallsAndFfiSteps primitive ffi state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory
    (.call none entry arguments) (memoryAccess := memoryAccess)
    (contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
      state.parameterShapes))
    (memoryHandler := memoryHandler)
  match lookupInfo entry state.returnShapes, result with
  | some shape, (.returned locals globals memory [value], steps) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory [value], steps)
      else none
  | some _, (.returned _ _ _ _, _) => none
  | _, (result, steps) => some (result, steps)

end Flapjack
