import SteppedFlapjack.PanValueFfiSemantics
/-!
# Resource accounting for structured Pancake

`PanValueSteppedResult` deliberately predates resource accounting and carries
only a source-step count.  This file adds the richer result requested by the
source-level resource users without changing that established API.

The evaluator below follows the same successful control-flow paths as the
source evaluator.  `maxCallDepth` is the active source-call depth (the
top-level program starts at depth zero), and `maxStoreAddress` is the largest
address written on that path.  A structured store observes its last flattened
word, so the result is useful even when the stored pointer is released before
the program returns.
-/

namespace Flapjack

structure PanCost (α : Type u) where
  steps : Nat
  maxCallDepth : Nat
  maxStoreAddress : Option α
  deriving Repr

abbrev PanValueCostResult (α : Type u) :=
  PanValueControlResult α × PanCost α

abbrev PanValueFfiCostResult (α : Type u) (σ : Type v) :=
  PanValueFfiControlResult α σ × PanCost α

def panCostAt (depth steps : Nat) : PanCost α :=
  { steps := steps, maxCallDepth := depth, maxStoreAddress := none }

def panCostMaxAddress [LT α] [DecidableRel (fun left right : α => left < right)] :
    Option α → Option α → Option α
  | none, right => right
  | left, none => left
  | some left, some right => some (if left < right then right else left)

def panCostCombine [LT α] [DecidableRel (fun left right : α => left < right)]
    (left right : PanCost α) : PanCost α :=
  { steps := left.steps + right.steps
    maxCallDepth := left.maxCallDepth.max right.maxCallDepth
    maxStoreAddress := panCostMaxAddress left.maxStoreAddress right.maxStoreAddress }

def panCostAddStep [LT α] [DecidableRel (fun left right : α => left < right)]
    (depth : Nat) (cost : PanCost α) : PanCost α :=
  panCostCombine cost (panCostAt depth 1)

def panCostObserveAddress [LT α] [DecidableRel (fun left right : α => left < right)]
    (address : α) (cost : PanCost α) : PanCost α :=
  { cost with maxStoreAddress :=
      panCostMaxAddress cost.maxStoreAddress (some address) }

def panValueFlatLastAddress [Add α]
    (bytesInWord address : α) (value : PanValue α) : Option α :=
  match panValueFlatWords value with
  | [] => none
  | words => some (panValueFlatOffset bytesInWord address (words.length - 1))

private def evalPanValueExpCost
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (depth : Nat) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expression : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (PanValue α × PanCost α) :=
  (evalPanValueExpCounted structs locals globals memory baseAddress topAddress
    bytesInWord expression memoryAccess).map fun (value, steps) =>
      (value, panCostAt depth steps)

private def evalPanValueExpsCost
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (depth : Nat) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expressions : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (List (PanValue α) × PanCost α) :=
  (evalPanValueExpsCounted structs locals globals memory baseAddress topAddress
    bytesInWord expressions memoryAccess).map fun (values, steps) =>
      (values, panCostAt depth steps)

mutual
  def evalPanValueCallWithCost
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) → Nat →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        Option (PanValueCostResult α)
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, depth, info, function, arguments,
        memoryAccess, contracts => do
        let (values, argumentCost) ← evalPanValueExpsCost depth structs locals globals
          memory baseAddress topAddress bytesInWord arguments memoryAccess
        let (parameters, body) ← lookupPanFunction function functions
        if panValueParametersValid structs contracts function values then
          let calleeLocals ← bindPanValueParameters parameters values
          let (result, bodyCost) ← evalPanValueProgWithCost primitive handler structs functions
            baseAddress topAddress bytesInWord fuel calleeLocals globals memory (depth + 1) body
            (memoryAccess := memoryAccess) (contracts := contracts)
          let cost := panCostCombine argumentCost bodyCost
          match result with
        | .normal _ _ _ => none
        | .returned _ calleeGlobals calleeMemory values =>
            -- HOL's Call checks only `shape_of retv <> return_sh`; the
            -- payload-size limit is enforced by the callee `Return`.
            if panValueReturnValid structs contracts function values then
              match info with
              | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory values, cost)
              | some (destination, _) => do
                  let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                    destination values (structs := structs)
                  pure (.normal locals globals calleeMemory, cost)
            else none
        | .raised _ calleeGlobals calleeMemory exception value =>
            if panValueExceptionValid structs contracts exception value &&
                panValuePayloadWithinLimit structs value then
              match info with
              | some (_, some (caught, handlerVariable, handlerProgram)) =>
                  if caught == exception then
                    if panValueHandlerValid structs contracts locals handlerVariable value then
                      let (handlerResult, handlerCost) ← evalPanValueProgWithCost
                        primitive handler structs functions baseAddress topAddress bytesInWord fuel
                        (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory
                        depth handlerProgram (memoryAccess := memoryAccess)
                        (contracts := contracts)
                      pure (handlerResult, panCostCombine cost handlerCost)
                    else none
                  else pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value, cost)
              | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value, cost)
            else none
        | .broke _ _ _ | .continued _ _ _ => none
        else none
    termination_by fuel _ _ _ _ _ _ _ _ _ => fuel

  def evalPanValueProgWithCost
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) → Nat →
        (program : Prog α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        Option (PanValueCostResult α)
    | 0, _, _, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, depth, .skip, _, _ =>
        some (.normal locals globals memory, panCostAt depth 1)
    | fuel + 1, locals, globals, memory, depth,
        .dec name shape value body, memoryAccess, contracts => do
        let (value, valueCost) ← evalPanValueExpCost depth structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let (result, bodyCost) ← evalPanValueProgWithCost primitive handler structs functions
            baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
            globals memory depth body (memoryAccess := memoryAccess) (contracts := contracts)
          pure (restorePanValueControlLocal name oldValue result,
            panCostAddStep depth (panCostCombine valueCost bodyCost))
        else none
    | _fuel + 1, locals, globals, memory, depth,
        .assign .local name value, memoryAccess, _contracts => do
        let (value, valueCost) ← evalPanValueExpCost depth structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValueAssignmentValid structs locals globals .local name value then
          pure (.normal (updatePanValueMap locals name value) globals memory,
            panCostAddStep depth valueCost)
        else none
    | _fuel + 1, locals, globals, memory, depth,
        .assign .global name value, memoryAccess, _contracts => do
        let (value, valueCost) ← evalPanValueExpCost depth structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValueAssignmentValid structs locals globals .global name value then
          pure (.normal locals (updatePanValueMap globals name value) memory,
            panCostAddStep depth valueCost)
        else none
    | _fuel + 1, locals, globals, memory, depth,
        .primitive name operator arguments, memoryAccess, _contracts => do
        let (values, valueCost) ← evalPanValueExpsCost depth structs locals globals memory
          baseAddress topAddress bytesInWord arguments memoryAccess
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory,
            panCostAddStep depth valueCost)
        else none
    | _fuel + 1, locals, globals, memory, depth,
        .store address value, memoryAccess, _contracts => do
        let (evaluatedAddress, addressCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord address memoryAccess
        let (evaluatedValue, valueCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord value memoryAccess
        let .word address := evaluatedAddress | none
        let memory ← panValueStoreWithAccess memory bytesInWord address evaluatedValue memoryAccess
        let cost := panCostAddStep depth (panCostCombine addressCost valueCost)
        pure (.normal locals globals memory,
          match panValueFlatLastAddress bytesInWord address evaluatedValue with
          | some last => panCostObserveAddress last cost
          | none => cost)
    | _fuel + 1, locals, globals, memory, depth,
        .store32 address value, memoryAccess, _contracts => do
        let (evaluatedAddress, addressCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord address memoryAccess
        let (evaluatedValue, valueCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord value memoryAccess
        let .word address := evaluatedAddress | none
        let .word value := evaluatedValue | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        let cost := panCostAddStep depth (panCostCombine addressCost valueCost)
        pure (.normal locals globals memory, panCostObserveAddress address cost)
    | _fuel + 1, locals, globals, memory, depth,
        .storeByte address value, memoryAccess, _contracts => do
        let (evaluatedAddress, addressCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord address memoryAccess
        let (evaluatedValue, valueCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord value memoryAccess
        let .word address := evaluatedAddress | none
        let .word value := evaluatedValue | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        let cost := panCostAddStep depth (panCostCombine addressCost valueCost)
        pure (.normal locals globals memory, panCostObserveAddress address cost)
    | fuel + 1, locals, globals, memory, depth,
        .seq first second, memoryAccess, contracts => do
        let (firstResult, firstCost) ← evalPanValueProgWithCost primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory depth first
          (memoryAccess := memoryAccess) (contracts := contracts)
        match firstResult with
        | .normal locals globals memory =>
            let (secondResult, secondCost) ← evalPanValueProgWithCost primitive handler structs functions
              baseAddress topAddress bytesInWord fuel locals globals memory depth second
              (memoryAccess := memoryAccess) (contracts := contracts)
            pure (secondResult, panCostAddStep depth (panCostCombine firstCost secondCost))
        | result => pure (result, panCostAddStep depth firstCost)
    | _fuel + 1, locals, globals, memory, depth,
        .ite condition thenBranch elseBranch, memoryAccess, contracts => do
        let (condition, conditionCost) ← evalPanValueExpCost depth structs locals globals memory
          baseAddress topAddress bytesInWord condition memoryAccess
        let .word condition := condition | none
        let (result, branchCost) ← if condition != 0 then
          evalPanValueProgWithCost primitive handler structs functions baseAddress topAddress
            bytesInWord _fuel locals globals memory depth thenBranch
            (memoryAccess := memoryAccess) (contracts := contracts)
        else
          evalPanValueProgWithCost primitive handler structs functions baseAddress topAddress
            bytesInWord _fuel locals globals memory depth elseBranch
            (memoryAccess := memoryAccess) (contracts := contracts)
        pure (result, panCostAddStep depth (panCostCombine conditionCost branchCost))
    | fuel + 1, locals, globals, memory, depth,
        .call info function arguments, memoryAccess, contracts => do
        let (result, callCost) ← evalPanValueCallWithCost primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory depth info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
        pure (result, panCostAddStep depth callCost)
    | fuel + 1, locals, globals, memory, depth,
        .decCall name shape function arguments body, memoryAccess, contracts => do
        let oldValue := locals name
        let (callResult, callCost) ← evalPanValueCallWithCost primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory depth none function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
        match callResult with
        | .returned _ globals memory [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyResult, bodyCost) ← evalPanValueProgWithCost primitive handler structs functions
                baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
                globals memory depth body (memoryAccess := memoryAccess) (contracts := contracts)
              pure (restorePanValueControlLocal name oldValue bodyResult,
                panCostAddStep depth (panCostCombine callCost bodyCost))
            else none
        | .raised _ globals memory exception value =>
            pure (.raised (fun _ => none) globals memory exception value,
              panCostAddStep depth callCost)
        | _ => none
    | _fuel + 1, locals, globals, memory, depth,
        .extCall function configuration configurationLength array arrayLength, memoryAccess,
        _contracts => do
        let (values, expressionCost) ← evalPanValueExpsCost depth structs locals globals memory
          baseAddress topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength] memoryAccess
        let [.word configuration, .word configurationLength, .word array, .word arrayLength] := values |
          none
        let locals ← handler function configuration configurationLength array arrayLength locals
        pure (.normal locals globals memory, panCostAddStep depth expressionCost)
    | fuel + 1, locals, globals, memory, depth,
        .while conditionExp body, memoryAccess, contracts => do
        let (condition, conditionCost) ← evalPanValueExpCost depth structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp memoryAccess
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory, panCostAddStep depth conditionCost)
        else
          let (bodyResult, bodyCost) ← evalPanValueProgWithCost primitive handler structs functions
            baseAddress topAddress bytesInWord fuel locals globals memory depth body
            (memoryAccess := memoryAccess) (contracts := contracts)
          match bodyResult with
          | .normal locals globals memory | .continued locals globals memory =>
              let (loopResult, loopCost) ← evalPanValueProgWithCost primitive handler structs functions
                baseAddress topAddress bytesInWord fuel locals globals memory depth (.while conditionExp body)
                (memoryAccess := memoryAccess) (contracts := contracts)
              pure (loopResult, panCostAddStep depth
                (panCostCombine conditionCost (panCostCombine bodyCost loopCost)))
          | .broke locals globals memory =>
              pure (.normal locals globals memory, panCostAddStep depth
                (panCostCombine conditionCost bodyCost))
          | result => pure (result, panCostAddStep depth
              (panCostCombine conditionCost bodyCost))
    | _fuel + 1, locals, globals, memory, depth, .break, _, _ =>
        pure (.broke locals globals memory, panCostAt depth 1)
    | _fuel + 1, locals, globals, memory, depth, .continue, _, _ =>
        pure (.continued locals globals memory, panCostAt depth 1)
    | _fuel + 1, locals, globals, memory, depth,
        .raise exception value, memoryAccess, contracts => do
        let (evaluatedValue, valueCost) ← evalPanValueExpCost depth structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValueExceptionValid structs contracts exception evaluatedValue &&
            panValuePayloadWithinLimit structs evaluatedValue then
          pure (.raised (fun _ => none) globals memory exception evaluatedValue,
            panCostAddStep depth valueCost)
        else none
    | _fuel + 1, locals, globals, memory, depth,
        .return value, memoryAccess, _contracts => do
        let (evaluatedValue, valueCost) ← evalPanValueExpCost depth structs locals globals memory
          baseAddress topAddress bytesInWord value memoryAccess
        if panValuePayloadWithinLimit structs evaluatedValue then
          pure (.returned (fun _ => none) globals memory [evaluatedValue],
            panCostAddStep depth valueCost)
        else none
    | _fuel + 1, locals, globals, memory, depth,
        .shMemLoad size kind name address, memoryAccess, _contracts => do
        let (evaluatedAddress, addressCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord address memoryAccess
        let .word evaluatedAddress := evaluatedAddress | none
        let value ← match memoryAccess with
          | none => memory evaluatedAddress
          | some access => access.sharedRead memory bytesInWord size evaluatedAddress
        if panValueSharedLoadValid structs locals globals kind name value then
          match kind with
          | .local => pure (.normal (updatePanValueMap locals name value) globals memory,
              panCostAddStep depth addressCost)
          | .global => pure (.normal locals (updatePanValueMap globals name value) memory,
              panCostAddStep depth addressCost)
        else none
    | _fuel + 1, locals, globals, memory, depth,
        .shMemStore size address value, memoryAccess, _contracts => do
        let (evaluatedAddress, addressCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord address memoryAccess
        let (evaluatedValue, valueCost) ← evalPanValueExpCost depth structs locals globals
          memory baseAddress topAddress bytesInWord value memoryAccess
        let .word evaluatedAddress := evaluatedAddress | none
        let .word evaluatedValue := evaluatedValue | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory evaluatedAddress (.word evaluatedValue))
          | some access =>
              (access.sharedStore memory bytesInWord size evaluatedAddress (.word evaluatedValue))
        let cost := panCostAddStep depth (panCostCombine addressCost valueCost)
        pure (.normal locals globals memory, panCostObserveAddress evaluatedAddress cost)
    | _fuel + 1, locals, globals, memory, depth,
        .tick, _, _ | _fuel + 1, locals, globals, memory, depth, .annot _ _, _, _ =>
        pure (.normal locals globals memory, panCostAt depth 1)
    termination_by fuel _ _ _ _ _ _ => fuel
end

def evalPanValueCostProg
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (PanValueCostResult α) :=
  evalPanValueProgWithCost primitive handler structs functions baseAddress topAddress bytesInWord
    fuel locals globals memory 0 program (memoryAccess := memoryAccess)

def evalPanValueCostProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (PanValueCostResult α) := do
  let state ← evalPanValueDeclarations initial declarations (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  let result ← evalPanValueCallWithCost primitive ffi state.structs state.functions
    state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory 0 none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
  match lookupInfo entry state.returnShapes, result with
  | some shape, (.returned locals globals memory [value], cost) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory [value], cost)
      else none
  | some _, (.returned _ _ _ _, _) => none
  | _, (result, cost) => some (result, cost)

/-! This conversion is the compatibility bridge for the stateful FFI API.
The dedicated FFI evaluator will use the same accounting fields once its
byte-range memory provenance is exposed. -/
def panValueFfiSteppedToCost (result : PanValueFfiSteppedResult α σ) :
    PanValueFfiCostResult α σ :=
  (result.1, { steps := result.2, maxCallDepth := 0, maxStoreAddress := none })

end Flapjack
