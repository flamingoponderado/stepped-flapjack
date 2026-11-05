import SteppedFlapjack.PanValueFfiClockShift
import SteppedFlapjack.PanValueFfiSemantics

/-!
# Clocked leaves and the stepped evaluator

The clocked semantics (`PanValueFfiClockSemantics`) evaluates simple statements
with its own leaf clauses.  The theorems here relate those leaves to the
stepped evaluator `evalPanValueFfiProgSteps` at unit fuel.  They depend on the
stepped semantics and move with it (issue #1251).
-/

namespace Flapjack

/-! Bridge to the stepped evaluator.  On leaf statements, the clocked leaf
    control result is the control result of the stepped evaluator at unit
    fuel.  The clocked semantics no longer delegates to the stepped one
    (issue #1251); this equation relates the two. -/
theorem evalPanValueFfiLeafControl_eq_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (hleaf : PanValueFfiLeafProg program)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiLeafControl context primitive handler structs baseAddress topAddress
      bytesInWord locals globals memory ffi program memoryAccess contracts memoryHandler =
      (evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord 1 locals globals memory ffi program
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler)).map Prod.fst := by
  cases hleaf
  case' assign kind _ _ => cases kind
  all_goals simp [evalPanValueFfiLeafControl, evalPanValueFfiProgSteps,
    panValueAssignLocalSteps_fst, panValueAssignGlobalSteps_fst,
    panValuePrimitiveSteps_fst, panValueStoreSteps_fst, panValueStore32Steps_fst,
    panValueStoreByteSteps_fst, panValueShMemLoadSteps_fst, panValueShMemStoreSteps_fst,
    panValueReturnSteps_fst, panValueRaiseSteps_fst, panValueFfiExtCallSteps_fst]

theorem evalPanValueFfiClockLeaf_clock
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (_fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (clockValue : Nat) (hleaf : PanValueFfiLeafProg program)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none) :
    (evalPanValueFfiClockLeaf context primitive handler structs
      baseAddress topAddress bytesInWord clockValue locals globals memory ffi
      program (memoryAccess := memoryAccess) (contracts := contracts)).map Prod.snd =
      (evalPanValueFfiProgSteps context primitive handler structs functions
        baseAddress topAddress bytesInWord 1 locals globals memory ffi program
        (memoryAccess := memoryAccess) (contracts := contracts)).map
        (fun _ => clockValue) := by
  simp [evalPanValueFfiClockLeaf, Function.comp_def,
    evalPanValueFfiLeafControl_eq_steps context primitive handler structs functions
      baseAddress topAddress bytesInWord locals globals memory ffi program hleaf
      memoryAccess contracts]

/-! The leaf adapter also preserves the terminal FFI branch exactly.  This is
    the source-side counterpart of the \`panSem\` ExtCall/shared-memory
    \`FinalFFI\` equations (cakeml/pancake/semantics/panSemScript.sml:716-730):
    the stepped evaluator supplies the complete post-state and event, while
    the clocked leaf only attaches the unchanged remaining clock. -/
theorem evalPanValueFfiClockLeaf_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (clock : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (hleaf : PanValueFfiLeafProg program)
    (finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (event : FfiFinalEvent) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.finalFfi finalLocals finalGlobals finalMemory finalFfi event, steps)) :
    evalPanValueFfiClockLeaf context primitive handler structs
      baseAddress topAddress bytesInWord clock locals globals memory ffi program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi finalLocals finalGlobals finalMemory finalFfi event), clock) := by
  simp [evalPanValueFfiClockLeaf,
    evalPanValueFfiLeafControl_eq_steps context primitive handler structs functions
      baseAddress topAddress bytesInWord locals globals memory ffi program hleaf
      memoryAccess contracts memoryHandler, hsteps]

/-! This is the direct `ExtCall` branch of Cake's `pc_compile_correct`.
    The source leaf evaluator's terminal FFI event crosses the clocked program
    boundary unchanged, with only the remaining clock attached. -/
theorem evalPanValueFfiClockProg_extCall_finalFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (_fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (configuration configurationLength array arrayLength : Exp α)
    (finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (event : FfiFinalEvent) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.finalFfi finalLocals finalGlobals finalMemory finalFfi event, steps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (_fuel + 1) locals globals memory ffi clock
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi finalLocals finalGlobals finalMemory finalFfi event), clock) := by
  simpa [evalPanValueFfiClockProg] using
    (evalPanValueFfiClockLeaf_finalFfi context primitive handler structs functions
      baseAddress topAddress bytesInWord clock locals globals memory ffi
      (.extCall function configuration configurationLength array arrayLength)
      (PanValueFfiLeafProg.extCall function configuration configurationLength array arrayLength)
      finalLocals finalGlobals finalMemory finalFfi event steps
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) hsteps)

/-! Cross-clock ExtCall FinalFFI preserves the exact event and post-state;
    only the remaining clock attached by the leaf shifts. -/
theorem evalPanValueFfiClockProg_extCall_finalFfi_cross_clock
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock ck : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (configuration configurationLength array arrayLength : Exp α)
    (finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (event : FfiFinalEvent) (steps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 locals globals memory ffi
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.finalFfi finalLocals finalGlobals finalMemory finalFfi event, steps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi finalLocals finalGlobals finalMemory finalFfi event), clock) ∧
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi (clock + ck)
      (.extCall function configuration configurationLength array arrayLength)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.finalFfi finalLocals finalGlobals finalMemory finalFfi event), clock + ck) := by
  constructor
  · exact evalPanValueFfiClockProg_extCall_finalFfi context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock locals globals memory ffi
      function configuration configurationLength array arrayLength finalLocals finalGlobals
      finalMemory finalFfi event steps (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) hsteps
  · exact evalPanValueFfiClockProg_extCall_finalFfi context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel (clock + ck) locals globals memory ffi
      function configuration configurationLength array arrayLength finalLocals finalGlobals
      finalMemory finalFfi event steps (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) hsteps

end Flapjack
