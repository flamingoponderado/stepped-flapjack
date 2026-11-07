import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.Concrete.SupportedSpan

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

/-- The observable result of a call to a supported body: a fallthrough is a
call error; a word return is preserved. -/
inductive CountedEntryExit {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Option (BitVec 64) → Prop
  | normal (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) :
      CountedEntryExit (.normal locals globals memory ffi) none
  | returned (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (word : BitVec 64) :
      CountedEntryExit (.returned locals globals memory ffi [.word word]) (some word)

/-- Every non-error counted body run reaches the generated entry within a
concrete code-derived bound. The exit relation records whether the function
returned a word or fell through; the generated call reports fallthrough as
an error, just as the source function-call semantics does. -/
theorem supported_counted_full_frontend_exit {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (topOutside : ¬ source.memaddrs source.topAddr) (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (entryName (progToHOL program),([],progToHOL program,.one)))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (nonerror : CountedNonError result) (countBound : count ≤ n) (clock : source.clock = n) :
    let body := progToHOL (panSimpProg program)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ exit targetFinal,
      CountedEntryExit result exit ∧
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry =
        (bodyExitEntry exit,targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + sizeOf (compileProgExactHOLW callee body) *
          (sizeOf (compileProgExactHOLW callee body) * (n+1)) := by
  obtain ⟨holResult,sourceFinal,sourceRun,outcome,_,_⟩ := supported_counted_source supported.1 production source rel ranged words
    supported.2 context primitive handler functions fuel count result run (by omega)
  cases outcome with
  | normal l g m f final finalRel finalRanged finalWords =>
    have span := supported_full_frontend_exit_clock program supported source sourceFinal locals globals structs exceptions
      topOutside aligned sourceCode none sourceRun
    obtain ⟨targetFinal,targetRun,bound⟩ := span
    exact ⟨none,targetFinal,.normal l g m f,targetRun,by simpa [clock] using bound⟩
  | returned l g m f word final finalRel finalRanged finalWords =>
    have span := supported_full_frontend_exit_clock program supported source sourceFinal locals globals structs exceptions
      topOutside aligned sourceCode (some word) sourceRun
    obtain ⟨targetFinal,targetRun,bound⟩ := span
    exact ⟨some word,targetFinal,.returned l g m f word,targetRun,by simpa [clock] using bound⟩
  | error l g m f final finalRel finalRanged finalWords =>
    exact False.elim nonerror

/-- A counted source run bounded by `n` reaches the actual generated entry
point within a bound calculated from `n` and the generated function body. -/
theorem supported_counted_full_frontend {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (topOutside : ¬ source.memaddrs source.topAddr) (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (entryName (progToHOL program),([],progToHOL program,.one)))
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
        3 + sizeOf (compileProgExactHOLW callee body) *
          (sizeOf (compileProgExactHOLW callee body) * (n+1)) := by
  obtain ⟨exit,targetFinal,outcome,targetRun,bound⟩ := supported_counted_full_frontend_exit program supported production source
    rel ranged words locals globals structs exceptions topOutside aligned sourceCode context primitive handler functions fuel count n
    (.returned postLocals postGlobals postMemory postFfi [.word word]) run (by trivial) countBound clock
  cases outcome with
  | returned l g m f value =>
    exact ⟨targetFinal,targetRun,bound⟩

end SteppedFlapjack.Concrete
