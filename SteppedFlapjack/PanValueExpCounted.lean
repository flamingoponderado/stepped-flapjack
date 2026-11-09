import Flapjack.PanSteppedSemantics

namespace Flapjack

/-- Counted fields with the same explicit memory route as individual expressions. -/
def evalPanValueFieldsCountedWithAccess [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α)) (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (List (FieldName × PanValue α) × Nat) :=
  (evalPanValueExp.evalPanValueFields structs locals globals memory baseAddress topAddress bytesInWord fields
    (memoryAccess := memoryAccess)).map (fun values => (values, panValueFieldsStepCost fields))

end Flapjack
