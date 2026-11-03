module

public import Flapjack.PanExpressionEvaluatorBase
public import SteppedFlapjack.PanValueExpCounted
@[expose] public section

namespace Flapjack

def evalPanValueExpCountedWith [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (route : Option (PanExprEvaluator α)) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (e : Exp α) (access : Option (PanValueMemoryAccess α)) :
    Option (PanValue α × Nat) :=
  match route with
  | none => evalPanValueExpCounted structs locals globals memory base top bytes e access
  | some run => (run structs locals globals memory base top bytes access e).map
      (fun v => (v, panValueExpStepCost e))

def evalPanValueExpsCountedWith [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (route : Option (PanExprEvaluator α)) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (es : List (Exp α)) (access : Option (PanValueMemoryAccess α)) :
    Option (List (PanValue α) × Nat) :=
  match route with
  | none => evalPanValueExpsCounted structs locals globals memory base top bytes es access
  | some run => (es.mapM (run structs locals globals memory base top bytes access)).map
      (fun vs => (vs, panValueExpsStepCost es))

@[simp] theorem evalPanValueExpCountedWith_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (base top bytes : α)
    (es : Exp α) (access : Option (PanValueMemoryAccess α)) :
    evalPanValueExpCountedWith none structs locals globals memory base top bytes es access =
      evalPanValueExpCounted structs locals globals memory base top bytes es access := rfl

@[simp] theorem evalPanValueExpsCountedWith_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (base top bytes : α)
    (es : List (Exp α)) (access : Option (PanValueMemoryAccess α)) :
    evalPanValueExpsCountedWith none structs locals globals memory base top bytes es access =
      evalPanValueExpsCounted structs locals globals memory base top bytes es access := rfl

/-- A pointwise-correct route preserves the counted single-expression result. -/
theorem evalPanValueExpCountedWith_some_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (run : PanExprEvaluator α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (h : ∀ e, run structs locals globals memory base top bytes access e =
      evalPanValueExp structs locals globals memory base top bytes e access)
    (e : Exp α) :
    evalPanValueExpCountedWith (some run) structs locals globals memory base top bytes e access =
      evalPanValueExpCounted structs locals globals memory base top bytes e access := by
  simp [evalPanValueExpCountedWith, evalPanValueExpCounted, h]

/-- A pointwise-correct route preserves the counted argument-list result. -/
theorem evalPanValueExpsCountedWith_some_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (run : PanExprEvaluator α) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (h : ∀ e, run structs locals globals memory base top bytes access e =
      evalPanValueExp structs locals globals memory base top bytes e access)
    (es : List (Exp α)) :
    evalPanValueExpsCountedWith (some run) structs locals globals memory base top bytes es access =
      evalPanValueExpsCounted structs locals globals memory base top bytes es access := by
  have hlist := evalPanValueExpsWith_some_eq run structs locals globals memory base top bytes access h es
  simpa [evalPanValueExpsCountedWith, evalPanValueExpsWith, evalPanValueExpsCounted] using
    congrArg (Option.map (fun vs => (vs, panValueExpsStepCost es))) hlist

/-- The counted result is the uncounted result paired with the static step
    cost of the expression. -/
theorem evalPanValueExpCountedWith_eq_map
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (route : Option (PanExprEvaluator α)) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (e : Exp α) (access : Option (PanValueMemoryAccess α)) :
    evalPanValueExpCountedWith route structs locals globals memory base top bytes e access =
      (evalPanValueExpWith route structs locals globals memory base top bytes e access).map
        (fun v => (v, panValueExpStepCost e)) := by
  cases route <;> rfl

/-- The counted list result is the uncounted one paired with the static step
    cost of the list. -/
theorem evalPanValueExpsCountedWith_eq_map
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (route : Option (PanExprEvaluator α)) (structs : StructContext)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (base top bytes : α) (es : List (Exp α)) (access : Option (PanValueMemoryAccess α)) :
    evalPanValueExpsCountedWith route structs locals globals memory base top bytes es access =
      (evalPanValueExpsWith route structs locals globals memory base top bytes es access).map
        (fun vs => (vs, panValueExpsStepCost es)) := by
  cases route <;> rfl

end Flapjack
