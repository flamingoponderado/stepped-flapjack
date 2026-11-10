import SteppedFlapjack.Concrete.ControlCodeIndependent
import SteppedFlapjack.Concrete.SimpVisits
import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.Concrete.SupportedSpan

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

/-- Every counted supported run, including errors, reaches the actual
simplified and global-lowered callee with the same source result. -/
theorem supported_counted_frontend_prefix {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let simplified := panSimpProg program
    let body := progToHOL simplified
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let simplifiedSource := panSimpSourceState program source
    let lower := callEntryStateHOLFinite (loweredStateFrom simplifiedSource body) HolFiniteMapExact.empty
    ∃ holResult sourceFinal,
      CountedOutcome production result holResult sourceFinal ∧
      lower.evaluateHOLFiniteState body =
        (holResult,{{sourceFinal with code := simplifiedSource.code} with code := (loweredStateFrom simplifiedSource body).code}) ∧
      controlSteps body lower ≤ n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body) := by
  let simplified := panSimpProg program
  let body := progToHOL simplified
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let simplifiedSource := panSimpSourceState program source
  let lower := callEntryStateHOLFinite (loweredStateFrom simplifiedSource body) HolFiniteMapExact.empty
  obtain ⟨holResult,sourceFinal,sourceRun,outcome,countedBound,_⟩ := supported_counted_source supported.1 production source
    rel ranged words supported.2 context primitive handler functions fuel count result run (by omega)
  let simplifiedFinal := {sourceFinal with code := simplifiedSource.code}
  have simpRun := supported_panSimp_run program supported source sourceFinal holResult sourceRun
  have shape := (supported_panSimp program supported).1
  have lowerRun := supported_globals_run_from simplified shape simplifiedSource simplifiedFinal holResult
    (by simpa [simplifiedSource,panSimpSourceState] using locals) simpRun
  have lowerEq : lower = {source with code := lower.code} := by
    simp [lower,loweredStateFrom,noGlobalsLoweredPreCall,callEntryStateHOLFinite,
      simplifiedSource,panSimpSourceState,locals]
  have independent := supported_control_code_irrel shape source lower.code
  have simplifiedBound := SimpVisits.supported_panSimp_controlSteps_compiled program supported callee source
  change controlSteps body source ≤ controlSteps (progToHOL program) source +
    CrepSteps.statementWeight (compileProgExactHOLW callee body) at simplifiedBound
  have bonusBound : countedErrorBonus result ≤ 1 := by
    cases result <;> simp [countedErrorBonus]
  refine ⟨holResult,sourceFinal,outcome,lowerRun,?_⟩
  change controlSteps body lower ≤ n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)
  rw [lowerEq,independent]
  change controlSteps body source ≤ n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)
  omega

/-- The observable result of a call to a supported body: a fallthrough is a
call error; a word return is preserved. -/
inductive CountedEntryExit {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Option (BitVec 64) → Prop
  | normal (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) :
      CountedEntryExit (.normal locals globals memory ffi) none
  | returned (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (word : BitVec 64) :
      CountedEntryExit (.returned locals globals memory ffi [.word word]) (some word)
  | error (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) :
      CountedEntryExit (.error locals globals memory ffi) none

/-- Error runs may require up to three compiled visits per source visit. -/
def countedFrontendFactor {σ : Type} (result : PanValueFfiControlResult (RiscV.Word 64) σ) : Nat :=
  1 + 2 * countedErrorBonus result

/-- Every counted body run reaches the generated entry within a
concrete code-derived bound. The exit relation records whether the function
returned a word, fell through, or errored; fallthrough and source errors
produce an error at the generated call entry. -/
theorem supported_counted_full_frontend_exit {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let body := progToHOL (panSimpProg program)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ exit targetFinal,
      CountedEntryExit result exit ∧
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry =
        (bodyExitEntry exit,targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + countedFrontendFactor result * CrepSteps.statementWeight (compileProgExactHOLW callee body) *
          (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) := by
  let simplified := panSimpProg program
  let body := progToHOL simplified
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let simplifiedSource := panSimpSourceState program source
  let lower := loweredStateFrom simplifiedSource body
  obtain ⟨holResult,sourceFinal,outcome,lowerRun,control⟩ := supported_counted_frontend_prefix program supported
    production source rel ranged words locals context primitive handler functions fuel count n result run countBound clock
  let lowerFinal := {{sourceFinal with code := simplifiedSource.code} with code := lower.code}
  have shape := (supported_panSimp program supported).1
  have sourceLocals : simplifiedSource.locals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using locals
  have sourceGlobals : simplifiedSource.globals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using globals
  have sourceStructs : simplifiedSource.structs = [] := by simpa [simplifiedSource,panSimpSourceState] using structs
  have sourceExceptions : simplifiedSource.eshapes = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using exceptions
  cases outcome with
  | normal l g m f final finalRel finalRanged finalWords =>
    have span := supported_entry_crep_exit_from simplified shape simplifiedSource sourceLocals sourceGlobals sourceStructs sourceExceptions
      lowerFinal none (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    obtain ⟨targetFinal,targetRun,bound,_⟩ := span
    exact ⟨none,targetFinal,.normal l g m f,targetRun,by simpa [countedFrontendFactor,countedErrorBonus] using bound⟩
  | returned l g m f word final finalRel finalRanged finalWords =>
    have span := supported_entry_crep_exit_from simplified shape simplifiedSource sourceLocals sourceGlobals sourceStructs sourceExceptions
      lowerFinal (some word) (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    obtain ⟨targetFinal,targetRun,bound,_⟩ := span
    exact ⟨some word,targetFinal,.returned l g m f word,targetRun,by simpa [countedFrontendFactor,countedErrorBonus] using bound⟩
  | error l g m f final finalRel finalRanged finalWords =>
    have span := supported_entry_crep_error_from simplified shape simplifiedSource sourceLocals sourceGlobals sourceStructs sourceExceptions
      lowerFinal (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    obtain ⟨targetFinal,targetRun,bound⟩ := span
    exact ⟨none,targetFinal,.error l g m f,targetRun,by simpa [countedFrontendFactor,countedErrorBonus,bodyExitEntry] using bound⟩

/-- A result-independent bound calculated from the generated code and source budget. -/
theorem supported_counted_full_frontend_uniform {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let body := progToHOL (panSimpProg program)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ exit targetFinal,
      CountedEntryExit result exit ∧
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry =
        (bodyExitEntry exit,targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + 3 * CrepSteps.statementWeight (compileProgExactHOLW callee body) *
          (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) := by
  obtain ⟨exit,targetFinal,outcome,targetRun,bound⟩ := supported_counted_full_frontend_exit
    program supported production source rel ranged words locals globals structs exceptions context primitive handler
    functions fuel count n result run countBound clock
  refine ⟨exit,targetFinal,outcome,targetRun,?_⟩
  have factorBound : countedFrontendFactor result ≤ 3 := by
    cases result <;> simp [countedFrontendFactor,countedErrorBonus]
  have scaled := Nat.mul_le_mul_right
    (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW (ctxtFcExactHOL
      (frontendContext (progToHOL (panSimpProg program))).funcs
      (frontendContext (progToHOL (panSimpProg program))).eids [] [] []) (progToHOL (panSimpProg program))))
    (Nat.mul_le_mul_right
      (CrepSteps.statementWeight (compileProgExactHOLW (ctxtFcExactHOL
        (frontendContext (progToHOL (panSimpProg program))).funcs
        (frontendContext (progToHOL (panSimpProg program))).eids [] [] []) (progToHOL (panSimpProg program))))
      factorBound)
  exact bound.trans (Nat.add_le_add_left scaled 3)

/-- A counted source run bounded by `n` reaches the actual generated entry
point within a bound calculated from `n` and the generated function body. -/
theorem supported_counted_full_frontend {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ) (word : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let body := progToHOL (panSimpProg program)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry =
        (some (.return [.word word]),targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + CrepSteps.statementWeight (compileProgExactHOLW callee body) *
          (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) ∧
      FfiStateRel postFfi targetFinal.ffi := by
  let simplified := panSimpProg program
  let body := progToHOL simplified
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let simplifiedSource := panSimpSourceState program source
  let lower := loweredStateFrom simplifiedSource body
  obtain ⟨holResult,sourceFinal,outcome,lowerRun,control⟩ := supported_counted_frontend_prefix program supported
    production source rel ranged words locals context primitive handler functions fuel count n
    (.returned postLocals postGlobals postMemory postFfi [.word word]) run countBound clock
  let lowerFinal := {{sourceFinal with code := simplifiedSource.code} with code := lower.code}
  have shape := (supported_panSimp program supported).1
  have sourceLocals : simplifiedSource.locals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using locals
  have sourceGlobals : simplifiedSource.globals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using globals
  have sourceStructs : simplifiedSource.structs = [] := by simpa [simplifiedSource,panSimpSourceState] using structs
  have sourceExceptions : simplifiedSource.eshapes = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using exceptions
  cases outcome with
  | returned l g m f value final finalRel finalRanged finalWords =>
    obtain ⟨targetFinal,targetRun,bound,ffi⟩ := supported_entry_crep_exit_from simplified shape simplifiedSource
      sourceLocals sourceGlobals sourceStructs sourceExceptions lowerFinal (some word)
      (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    have ffiRel : FfiStateRel postFfi sourceFinal.ffi := finalRel.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨targetFinal,targetRun,bound,?_⟩
    simpa [lowerFinal] using ffi ▸ ffiRel

end SteppedFlapjack.Concrete
