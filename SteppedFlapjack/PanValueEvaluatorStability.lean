import Flapjack.PanValues

namespace Flapjack

/-- Expression evaluation depends on local and global lookups only at names
    occurring in the expression. This infrastructure has no HOL declaration:
    it supports constructing a finite expression view of function-backed maps. -/
theorem evalPanValueExp_lookup_congr
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals locals' globals globals' : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (expression : Exp α) (access : Option (PanValueMemoryAccess α))
    (hloc : ∀ name ∈ expLocalVars expression, locals name = locals' name)
    (hglob : ∀ name ∈ expGlobalVars expression, globals name = globals' name) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression access =
      evalPanValueExp structs locals' globals' memory baseAddress topAddress bytesInWord expression access := by
  have hmain : ∀ expression access,
      (∀ name ∈ expLocalVars expression, locals name = locals' name) →
      (∀ name ∈ expGlobalVars expression, globals name = globals' name) →
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord expression access =
        evalPanValueExp structs locals' globals' memory baseAddress topAddress bytesInWord expression access := by
    apply evalPanValueExp.induct
      (motive1 := fun es access =>
        (∀ name ∈ expLocalVars.expLocalVarsList es, locals name = locals' name) →
        (∀ name ∈ expGlobalVars.expGlobalVarsList es, globals name = globals' name) →
        evalPanValueExp.evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord es access =
          evalPanValueExp.evalPanValueExps structs locals' globals' memory baseAddress topAddress bytesInWord es access)
      (motive2 := fun e access =>
        (∀ name ∈ expLocalVars e, locals name = locals' name) →
        (∀ name ∈ expGlobalVars e, globals name = globals' name) →
        evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e access =
          evalPanValueExp structs locals' globals' memory baseAddress topAddress bytesInWord e access)
      (motive3 := fun fs access =>
        (∀ name ∈ expLocalVars.expLocalVarsFieldList fs, locals name = locals' name) →
        (∀ name ∈ expGlobalVars.expGlobalVarsFieldList fs, globals name = globals' name) →
        evalPanValueExp.evalPanValueFields structs locals globals memory baseAddress topAddress bytesInWord fs access =
          evalPanValueExp.evalPanValueFields structs locals' globals' memory baseAddress topAddress bytesInWord fs access)
    all_goals
      intros
      simp_all [evalPanValueExp, evalPanValueExp.evalPanValueExps,
        evalPanValueExp.evalPanValueFields, expLocalVars, expLocalVars.expLocalVarsList,
        expLocalVars.expLocalVarsFieldList, expGlobalVars, expGlobalVars.expGlobalVarsList,
        expGlobalVars.expGlobalVarsFieldList, List.mem_append]
  exact hmain expression access hloc hglob


end Flapjack
