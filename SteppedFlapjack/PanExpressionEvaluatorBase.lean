import Flapjack.PanValues

namespace Flapjack

/-- A source expression evaluator receives the current program components.
The route is selected by the enclosing state-owned runner. -/
abbrev PanExprEvaluator (α : Type u) :=
  StructContext → (VarName → Option (PanValue α)) → (VarName → Option (PanValue α)) →
    (α → Option (PanValue α)) → α → α → α → Option (PanValueMemoryAccess α) →
      Exp α → Option (PanValue α)

/-- Evaluate with an optional selected route. Without a route, the existing
    generic evaluator remains the definitional default. -/
def evalPanValueExpWith [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (route : Option (PanExprEvaluator α)) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (e : Exp α) (access : Option (PanValueMemoryAccess α)) :
    Option (PanValue α) :=
  match route with
  | none => evalPanValueExp structs locals globals memory base top bytes e access
  | some run => run structs locals globals memory base top bytes access e

/-- List evaluation preserves the original left-to-right failure behavior. -/
def evalPanValueExpsWith [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (route : Option (PanExprEvaluator α)) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (es : List (Exp α)) (access : Option (PanValueMemoryAccess α)) :
    Option (List (PanValue α)) :=
  match route with
  | none => evalPanValueExps structs locals globals memory base top bytes es access
  | some run => es.mapM (run structs locals globals memory base top bytes access)

@[simp] theorem evalPanValueExpWith_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (base top bytes : α)
    (es : Exp α) (access : Option (PanValueMemoryAccess α)) :
    evalPanValueExpWith none structs locals globals memory base top bytes es access =
      evalPanValueExp structs locals globals memory base top bytes es access := rfl

@[simp] theorem evalPanValueExpsWith_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (base top bytes : α)
    (es : List (Exp α)) (access : Option (PanValueMemoryAccess α)) :
    evalPanValueExpsWith none structs locals globals memory base top bytes es access =
      evalPanValueExps structs locals globals memory base top bytes es access := rfl

/-- Pointwise agreement lifts through the source argument-list evaluator. -/
theorem evalPanValueExpsWith_some_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (run : PanExprEvaluator α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (h : ∀ e, run structs locals globals memory base top bytes access e =
      evalPanValueExp structs locals globals memory base top bytes e access)
    (es : List (Exp α)) :
    evalPanValueExpsWith (some run) structs locals globals memory base top bytes es access =
      evalPanValueExps structs locals globals memory base top bytes es access := by
  unfold evalPanValueExpsWith evalPanValueExps
  induction es with
  | nil => simp [evalPanValueExp.evalPanValueExps]
  | cons e es ih =>
      simp only [List.mapM_cons, evalPanValueExp.evalPanValueExps, h, ih]


end Flapjack
