import Flapjack.PanValueFfiClockProjection

namespace Flapjack

/-- The compatibility step evaluator has no clock: at zero clock, `Tick`
     succeeds there while the clocked evaluator times out. Consequently a
     clocked-to-stepped correspondence needs a non-timeout condition or a
     clock-aware step relation. This is Flapjack-specific infrastructure,
     not a port of a HOL declaration. -/
theorem tick_zero_clocked_and_stepped_differ
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0 .tick =
      some (.timeout (fun _ => none) globals memory ffi, 0) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi .tick =
      some (.normal locals globals memory ffi, 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, panValueFfiClockTimeout]
  · simp [evalPanValueFfiProgSteps]


end Flapjack
