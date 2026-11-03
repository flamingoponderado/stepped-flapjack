module

public import Flapjack.PanProgramSemantics

@[expose] public section

/-!
# Step-counted Pancake expression evaluation

A pure expression evaluator whose successful result also carries a
compositional source-step count: every expression node costs one step plus the
costs of its recursively evaluated operands, and list traversal is free.  The
`_fst` theorems show that dropping the count gives the ordinary
`evalPanValueExp` result.

This module is shared by the clocked semantics (`PanValueFfiClockSemantics`)
and the stepped statement semantics (`PanSteppedSemantics`,
`PanValueFfiSemantics`).  It contains no statement evaluator, so the clocked
side can use it without depending on the stepped semantics (issue #1251).
-/

namespace Flapjack

private def evalPanValueExpSteps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) : Exp α →
    Option (PanValue α × Nat)
  | .const value => some (.word value, 1)
  | .var .local name => (locals name).map (fun value => (value, 1))
  | .var .global name => (globals name).map (fun value => (value, 1))
  | .rStruct fields => do
      let (values, steps) ← evalPanValueExpSteps.evalExps structs locals globals
        memory baseAddress topAddress bytesInWord fields
      pure (.rStruct values, steps + 1)
  | .rField index expression => do
      let (value, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .rStruct fields =>
          let value ← fields[index]?
          pure (value, steps + 1)
      | _ => none
  | .nStruct name fields => do
      let info ← lookupInfo name structs
      let (values, steps) ← evalPanValueExpSteps.evalFields structs locals globals
        memory baseAddress topAddress bytesInWord fields
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values, steps + 1)
      else none
  | .nField name expression => do
      let (value, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            let value ← lookupPanValueField name fields
            pure (value, steps + 1)
          else none
      | _ => none
  | .load shape address => do
      let (address, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      if isWfShape structs shape && panShapeMatches (panValueShape structs value) shape then
        pure (value, steps + 1)
      else none
  | .load32 address | .loadByte address => do
      let (address, steps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      match value with
      | .word value => pure (.word value, steps + 1)
      | _ => none
  | .op operator arguments => do
      let (values, steps) ← evalPanValueExpSteps.evalExps structs locals globals
        memory baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] =>
          pure (.word (evalPanBinOp operator left right), steps + 1)
      | _ => none
  | .panOp operator arguments => do
      let (values, steps) ← evalPanValueExpSteps.evalExps structs locals globals
        memory baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => do
          let value ← evalPanOp operator [left, right]
          pure (.word value, steps + 1)
      | _ => none
  | .cmp operator left right => do
      let (left, leftSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord left
      let (right, rightSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          pure (.word (evalPanCmp operator left right), leftSteps + rightSteps + 1)
      | _, _ => none
  | .shift operator left right => do
      let (left, leftSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord left
      let (right, rightSteps) ← evalPanValueExpSteps structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          let value ← evalPanShift operator left right
          pure (.word value, leftSteps + rightSteps + 1)
      | _, _ => none
  | .baseAddr => some (.word baseAddress, 1)
  | .topAddr => some (.word topAddress, 1)
  | .bytesInWord => some (.word bytesInWord, 1)
termination_by expression => sizeOf expression
where
  evalExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) : List (Exp α) →
      Option (List (PanValue α) × Nat)
    | [] => some ([], 0)
    | expression :: expressions => do
        let (value, expressionSteps) ← evalPanValueExpSteps structs locals globals
          memory baseAddress topAddress bytesInWord expression
        let (values, restSteps) ← evalExps structs locals globals memory
          baseAddress topAddress bytesInWord expressions
        pure (value :: values, expressionSteps + restSteps)
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  evalFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      List (FieldName × Exp α) → Option (List (FieldName × PanValue α) × Nat)
    | [] => some ([], 0)
    | (name, expression) :: fields => do
        let (value, expressionSteps) ← evalPanValueExpSteps structs locals globals
          memory baseAddress topAddress bytesInWord expression
        let (values, restSteps) ← evalFields structs locals globals memory
          baseAddress topAddress bytesInWord fields
        pure ((name, value) :: values, expressionSteps + restSteps)
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

private def evalPanValueExpsSteps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α)) : Option (List (PanValue α) × Nat) :=
  evalPanValueExpSteps.evalExps structs locals globals memory
    baseAddress topAddress bytesInWord expressions

private def evalPanValueFieldsSteps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α)) :
    Option (List (FieldName × PanValue α) × Nat) :=
  evalPanValueExpSteps.evalFields structs locals globals memory
    baseAddress topAddress bytesInWord fields

def panValueExpStepCost : Exp α → Nat
  | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 1
  | .rStruct fields => panValueExpStepCost.panValueExpsStepCost fields + 1
  | .rField _ expression | .nField _ expression | .load32 expression |
      .loadByte expression => panValueExpStepCost expression + 1
  | .nStruct _ fields => panValueExpStepCost.panValueFieldsStepCost fields + 1
  | .load _ address => panValueExpStepCost address + 1
  | .op _ arguments | .panOp _ arguments =>
      panValueExpStepCost.panValueExpsStepCost arguments + 1
  | .cmp _ left right | .shift _ left right =>
      panValueExpStepCost left + panValueExpStepCost right + 1
termination_by expression => sizeOf expression
where
  panValueExpsStepCost : List (Exp α) → Nat
    | [] => 0
    | expression :: expressions =>
        panValueExpStepCost expression + panValueExpsStepCost expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  panValueFieldsStepCost : List (FieldName × Exp α) → Nat
    | [] => 0
    | (_, expression) :: fields =>
        panValueExpStepCost expression + panValueFieldsStepCost fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def panValueExpsStepCost (expressions : List (Exp α)) : Nat :=
  panValueExpStepCost.panValueExpsStepCost expressions

def panValueFieldsStepCost (fields : List (FieldName × Exp α)) : Nat :=
  panValueExpStepCost.panValueFieldsStepCost fields

def evalPanValueExpCounted [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expression : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (PanValue α × Nat) :=
  (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression
    memoryAccess).map
    (fun value => (value, panValueExpStepCost expression))

def evalPanValueExpsCounted [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expressions : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (List (PanValue α) × Nat) :=
  (evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord expressions
    memoryAccess).map
    (fun values => (values, panValueExpsStepCost expressions))

def evalPanValueFieldsCounted [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (List (FieldName × PanValue α) × Nat) :=
  (evalPanValueExp.evalPanValueFields structs locals globals memory
      baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)).map
    (fun values => (values, panValueFieldsStepCost fields))

theorem evalPanValueExpCounted_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expression : Exp α) :
    (evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      expression).map Prod.fst =
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression := by
  simp [evalPanValueExpCounted, Function.comp_def]

theorem evalPanValueExpCounted_snd
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expression : Exp α) :
    (evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      expression).map Prod.snd =
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        expression).map (fun _ => panValueExpStepCost expression) := by
  simp [evalPanValueExpCounted, Function.comp_def]

theorem evalPanValueExpsCounted_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expressions : List (Exp α)) :
    (evalPanValueExpsCounted structs locals globals memory baseAddress topAddress
      bytesInWord expressions).map (fun result => result.1) =
      evalPanValueExps structs locals globals memory baseAddress topAddress
        bytesInWord expressions := by
  simp [evalPanValueExpsCounted, Function.comp_def]

theorem evalPanValueExpsCounted_snd
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (expressions : List (Exp α)) :
    (evalPanValueExpsCounted structs locals globals memory baseAddress topAddress
      bytesInWord expressions).map Prod.snd =
      (evalPanValueExps structs locals globals memory baseAddress topAddress
        bytesInWord expressions).map (fun _ => panValueExpsStepCost expressions) := by
  simp [evalPanValueExpsCounted, Function.comp_def]

theorem evalPanValueFieldsCounted_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    (evalPanValueFieldsCounted structs locals globals memory baseAddress topAddress
      bytesInWord fields (memoryAccess := memoryAccess)).map (fun result => result.1) =
      evalPanValueExp.evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess) := by
  simp [evalPanValueFieldsCounted, Function.comp_def]

theorem evalPanValueFieldsCounted_snd
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    (evalPanValueFieldsCounted structs locals globals memory baseAddress topAddress
      bytesInWord fields (memoryAccess := memoryAccess)).map Prod.snd =
      (evalPanValueExp.evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)).map
        (fun _ => panValueFieldsStepCost fields) := by
  simp [evalPanValueFieldsCounted, Function.comp_def]

end Flapjack
