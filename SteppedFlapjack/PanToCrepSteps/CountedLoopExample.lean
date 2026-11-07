import Flapjack.Pancake.Proofs.PanToCrep
import SteppedFlapjack.PanToCrepSteps.CountedWhileTraceExample

/-! A state-changing loop checked across counted and HOL semantics.

This module is a reusable proof component for the concrete source-to-machine
example, so it is imported by the library.
-/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- Starting with a nonzero word-valued local, the loop reads it, writes
zero, and rechecks the condition. Its counted execution has six steps. -/
theorem counted_while_set_zero_example {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name)
    (initialWord : BitVec 64) (nonzero : initialWord ≠ 0)
    (initial : production.locals name = some (.word initialWord)) (clock : source.clock ≠ 0)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let post := setVarHOLFinite (ofString name) (.val (.word 0)) source.decClockHOLFinite
    let condition : Exp (RiscV.Word 64) := .var .local name
    let body : Prog (RiscV.Word 64) := .assign .local name (.const 0)
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
      production.locals production.globals production.memory production.ffi (.while condition body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal (updatePanValueMap production.locals name (.word 0)) production.globals production.memory production.ffi,6) ∧
    source.evaluateHOLFiniteState (.while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0))) = (none,post) ∧
    controlSteps (.while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0))) source ≤ 6 := by
  have trace := counted_while_set_zero_trace production source rel ranged name nameRanged initialWord nonzero initial clock
    context primitive handler functions fuel
  simpa [expToHOL] using counted_while_trace (.var .local name) (.assign .local name (.const 0))
    (.assign .local (ofString name) (.const 0)) context primitive handler functions trace


/-- In a context containing the local, the state-changing loop followed by a
constant return has the initialized loop-and-tail shape. Its HOL execution
returns the requested word and requires at most ten control visits. A
zero-argument entry starts with an empty local context and needs an enclosing
declaration before this result can instantiate the machine theorem. -/
theorem counted_set_zero_with_tail {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (initialWord : BitVec 64) (nonzero : initialWord ≠ 0)
    (initial : production.locals name = some (.word initialWord)) (clock : source.clock ≠ 0)
    (returned : BitVec 64) (ctxt : PanToCrepContextExact 64) (localIndex : Nat)
    (localFound : ctxt.vars.lookup (ofString name) = some (.one,[localIndex]))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let post := setVarHOLFinite (ofString name) (.val (.word 0)) source.decClockHOLFinite
    let loop : ProgHOL 64 := .while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0))
    let program : ProgHOL 64 := .seq .skip (.seq loop (.return (.const returned)))
    BranchProgram ctxt .skip ∧ ScalarExpression ctxt (.var .local (ofString name)) ∧
    BranchProgram ctxt (.assign .local (ofString name) (.const 0)) ∧
    BranchProgram ctxt (.return (.const returned)) ∧
    source.evaluateHOLFiniteState program = (some (.returned (.val (.word returned))),emptyLocalsHOLFinite post) ∧
    controlSteps program source ≤ 10 := by
  obtain ⟨_,loopRun,loopBound⟩ := counted_while_set_zero_example production source rel ranged name nameRanged
    initialWord nonzero initial clock context primitive handler functions fuel
  refine ⟨.skip,.local _ _ localFound,.assign _ _ localFound (.const _),.return (.const _),?_,?_⟩
  · rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,loopRun]
    dsimp only
    rw [evaluateHOLFiniteState_return]
    simp [evalHOLExact,shapeOfHOLExact]
  · rw [controlSteps_seq,evaluateHOLFiniteState_skip]
    dsimp only
    rw [controlSteps_seq,loopRun]
    dsimp only
    have skipCount : controlSteps (.skip : ProgHOL 64) source = 1 := by rw [controlSteps.eq_def]; rfl
    have retCount : controlSteps (.return (.const returned) : ProgHOL 64)
        (setVarHOLFinite (ofString name) (.val (.word 0)) source.decClockHOLFinite) = 1 := by
      rw [controlSteps.eq_def]
      rfl
    simp only [skipCount,retCount]
    omega


/-- The zero-argument callee context used by the machine theorem has no local
bindings, so a local-variable loop needs a surrounding declaration. -/
theorem zero_arg_context_has_no_locals {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name : MlS) :
    (ctxtFcExactHOL ctxt.funcs ctxt.eids [] [] []).vars.lookup name = none := by
  simp [ctxtFcExactHOL,HolFiniteMapExact.updateList,FUPDATE_LIST,HolFiniteMapExact.empty]

end SteppedFlapjack.PanToCrepSteps
