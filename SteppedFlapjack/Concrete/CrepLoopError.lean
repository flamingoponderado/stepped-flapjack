import SteppedFlapjack.Concrete.WitnessLoopCode

/-! The compiler does not preserve arbitrary malformed Crep errors. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps

/-- Even with the ordinary state, memory, globals, code and locals relations,
an assignment to an unbound source local errors while its optimized compiled
code succeeds, for every target clock. A result-preserving span therefore
needs a source-side safety condition or a completed, non-error source run. -/
theorem unbound_assignment_not_preserved {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) :
    let crep := crepStateFrom source branchingHOL
    let ctxt := witnessLoopContext arch branchingHOL
    let target := loopStateFrom arch source branchingHOL
    let program : CrepProgHOL 64 := .assign 1 (.const 0)
    ScalarProgram program ∧
    crepToLoopStateRelExact crep target ∧
    crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs ∧
    crepToLoopGlobalsRelHOLExact crep.globals target.globals ∧
    crepToLoopCodeRelExact ctxt crep.code target.code ∧
    crepToLoopLocalsRelExact ctxt .ln crep.locals target.locals ∧
    (evalCrepSemHOLProgExact crep program).1 = some .error ∧
    ∀ clock, (evaluate (optimiseHOL (compileHOLExact ctxt .ln program)) {target with clock := clock}).1 = none := by
  have rel := loopStateFrom_relations arch source branchingHOL
  have codeLocals := branching_loop_code_locals arch source
  refine ⟨.assign 1 (.direct (.const 0)),rel.1,rel.2.1,rel.2.2,codeLocals.1,codeLocals.2,?_,?_⟩
  · rw [evalCrepSemHOLProgExact_assign_holShape]
    simp [crepStateFrom,PanToCrepSteps.concreteDeclCrepState,evalCrepSemHOLExp,HolFiniteMapExact.empty]
  · intro clock
    simp [witnessLoopContext,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq,
      HolFiniteMapExact.empty,compileHOLExact,optimiseHOL,loopCallCompHOL,compHOL,shrinkHOL,markAllHOL,evaluate]
end SteppedFlapjack.Concrete
