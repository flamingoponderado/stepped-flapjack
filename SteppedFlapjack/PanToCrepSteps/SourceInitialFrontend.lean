import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals

/-! Source-first initial states for the no-global frontend. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open SteppedFlapjack.CrepToLoopSteps

/-- Starting from a source entry with empty locals, globals, exceptions and
structures, construct related Pancake, Crep and Loop states with the supplied
compiled code tables. The global-code premise states the compiler's per-code
lookup property; the Crep and Loop code tables are installed directly. -/
theorem noGlobals_source_frontend {σ : Type}
    (source : PanSemStateFiniteExact 64 σ)
    (panCode : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (locals : source.locals = HolFiniteMapExact.empty)
    (globals : source.globals = HolFiniteMapExact.empty)
    (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (structs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (callerVars : caller.vars = HolFiniteMapExact.empty)
    (callerExceptions : caller.eids = HolFiniteMapExact.empty)
    (loopVars : loopCtxt.vars = HolFiniteMapExact.empty)
    (codeCompiled : ∀ function parameters program returnShape,
      source.code.lookup function = some (parameters,program,returnShape) →
      panCode.lookup function = some (parameters,compileProgExactHOL emptyGlobalsContext program,returnShape)) :
    let pan := noGlobalsLoweredPreCall source panCode
    let crep := concreteDeclCrepState pan programs
    let target := concreteDeclLoopState arch crep programs
    pan.evaluateHOLFiniteState (nestedSeqHOL []) = (none,pan) ∧
    pan.clock ≠ 0 ∧
    panGlobalsStateRelHOLExact true emptyGlobalsContext source
      (callEntryStateHOLFinite pan HolFiniteMapExact.empty) ∧
    panToCrepStateRelFiniteExact pan crep ∧
    crep.code = alistToFmapCodeExact programs ∧
    panToCrepExcpRelFiniteExact caller.eids pan.eshapes ∧
    panToCrepLocalsRelFiniteExact caller pan.locals crep.locals ∧
    crepToLoopStateRelExact crep target ∧
    crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs ∧
    crepToLoopGlobalsRelHOLExact crep.globals target.globals ∧
    crepToLoopLocalsRelExact loopCtxt .ln crep.locals target.locals ∧
    target.code = sptFromAList (compileProgHOLExact arch programs) := by
  let pan := noGlobalsLoweredPreCall source panCode
  let crep := concreteDeclCrepState pan programs
  let target := concreteDeclLoopState arch crep programs
  have stateRel : panToCrepStateRelFiniteExact pan crep := by
    apply concreteDecl_panCrep_stateRel
    · simpa [pan,noGlobalsLoweredPreCall] using structs
    · simpa [pan,noGlobalsLoweredPreCall] using globals
  have crepRelations := concreteDecl_crepLoop_relations arch crep programs (by simp [crep,concreteDeclCrepState])
  refine ⟨evaluateHOLFiniteState_skip _,?_,?_,stateRel,rfl,?_,?_,crepRelations.1,
    crepRelations.2.1,crepRelations.2.2,?_,rfl⟩
  · simp [noGlobalsLoweredPreCall]
  · exact noGlobals_source_callEntry_rel source panCode locals globals structs topOutside aligned codeCompiled
  · simpa [pan,noGlobalsLoweredPreCall,exceptions,callerExceptions] using (empty_panCrep_exceptions (width := 64))
  · simpa [pan,crep,noGlobalsLoweredPreCall,concreteDeclCrepState,locals] using empty_panCrep_locals caller crep.locals callerVars
  · simpa [target,crep,concreteDeclLoopState,concreteDeclCrepState] using empty_crepLoop_locals loopCtxt target.locals loopVars

end SteppedFlapjack.PanToCrepSteps
