import SteppedFlapjack.Concrete.WitnessLoopCode
import SteppedFlapjack.Concrete.CountedApplications
import SteppedFlapjack.Concrete.ScalarEntry

/-! Generated code for the supported Phase 7 frontend. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.Compiler.Encoders.Asm Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

def supportedCallee (body : ProgHOL 64) : CrepProgHOL 64 :=
  let caller := frontendContext body
  compileProgExactHOLW (ctxtFcExactHOL caller.funcs caller.eids [] [] []) body

/-- The actual generated singleton program contains its entry and compiled body. -/
theorem supported_crepPrograms (program : Prog (RiscV.Word 64)) (supported : Supported program) :
    crepPrograms (progToHOL program) =
      twoPrograms (ofString "main") (entryName (progToHOL program)) (supportedCallee (progToHOL program)) := by
  let body := progToHOL program
  have renameEq : fpermHOL (ofString "main") (entryName body) body = body := supported_fperm supported _ _
  have renameEq' : fpermHOL (ofString "main") (newMainNameHOL (singleEntryProgram (ofString "main") body)) body = body := by
    simpa [entryName] using renameEq
  have globalEq : compileProgExactHOL emptyGlobalsContext body = body := supported_globals_fixed supported _
  change crepPrograms body = twoPrograms (ofString "main") (entryName body) (supportedCallee body)
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp [twoPrograms, supportedCallee, frontendContext, declarations, singleEntry_compileTop, entryName,
    compileToCrepExactHOLW, functionsHOL, compFuncExactHOLW, compileProgExactHOLW,
    compileCallNoReturnExactHOLW, compileExpExactHOLWList, crepVarsHOL, renameEq', globalEq, ctxtFcExactHOL, panToCrepMakeVmapHOLExact, mkCtxtExactHOL, maxList]

/-- A supported singleton generates a scalar Crep callee. -/
theorem supportedCallee_scalar (program : Prog (RiscV.Word 64)) (supported : Supported program) :
    ScalarProgram (supportedCallee (progToHOL program)) :=
  supported_compiled_scalar program supported _ (supported_crepPrograms program supported)

/-- A returning supported Crep entry reaches its actual optimized Loop entry
at a bound calculated from the compiled callee and the Crep visit limit. -/
theorem supported_entry_loop {σ : Type} (arch : AsmArchitecture)
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ) (entryFinal : CrepSemHOLState 64 σ)
    (values : List (HolWordLab 64)) (limit : Nat)
    (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact (crepStateFrom source (progToHOL program)).memory memory
      (crepStateFrom source (progToHOL program)).memaddrs)
    (nonzero : (crepStateFrom source (progToHOL program)).clock ≠ 0)
    (entryRun : evalCrepSemHOLProgExact (crepStateFrom source (progToHOL program))
      (.seq .skip (.call none (entryName (progToHOL program)) [])) = (some (.return values),entryFinal))
    (entryBound : CrepSteps.steps (.seq .skip (.call none (entryName (progToHOL program)) []))
      (crepStateFrom source (progToHOL program)) ≤ limit) :
    let body := progToHOL program
    let target := {(loopStateFrom arch source body) with memory := memory}
    let ctxt := witnessLoopContext arch body
    let code := compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln (supportedCallee body)
    let budget := 3*loopVisitWeight (optimiseHOL code)*(limit+1)
    ∃ post,
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms body) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+budget} =
        (some (.result (values.map wlabWlocExact)),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+budget} ≤
        loopVisitWeight (optimiseHOL code)*(limit+budget+1)+8 ∧
      crepToLoopStateRelExact entryFinal {post with clock := entryFinal.clock} ∧
      crepToLoopMemRelHOLExact entryFinal.memory post.memory entryFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact entryFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt entryFinal.code post.code := by
  let body := progToHOL program
  let crep := crepStateFrom source body
  let target := {(loopStateFrom arch source body) with memory := memory}
  let ctxt := witnessLoopContext arch body
  let name := entryName body
  let p := supportedCallee body
  have code := supported_crepPrograms program supported
  have scalar := supportedCallee_scalar program supported
  have fresh : ofString "main" ≠ name := Ne.symm (entryName_fresh body)
  have found : crep.code.lookup name = some ([],p) := by
    have h := generated_callee_lookup body p code
    simpa [crep,name,crepState,crepStateFrom,PanToCrepSteps.concreteDeclCrepState] using h
  have label : findLabExact ctxt name = 65 := by
    have h := twoPrograms_callee_label arch (ofString "main") name p fresh
    change findLabExact (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (crepPrograms body)) 0) name = 65
    rw [show crepPrograms body = twoPrograms (ofString "main") name p from code]
    exact h
  have originalRel := loopStateFrom_relations arch source body
  have codeLocals := loopStateFrom_code_locals arch source body p scalar code
  have result := generatedScalar_entry_explicit ctxt name p scalar crep entryFinal target values limit
    nonzero found entryRun entryBound originalRel.1 memoryRel originalRel.2.2 codeLocals.1 codeLocals.2 label
  obtain ⟨post,run,bound,state,mem,globals,finalCode⟩ := result
  have entry : (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms body) := by
    rw [code, (twoLoopPrograms_eq arch _ _ p scalar).symm]
    exact twoLoopPrograms_entry_code arch _ _ _ fresh
  exact ⟨post,entry,run,bound,state,mem,globals,finalCode⟩

/-- Static Crep visit budget for a source run of at most `n` visits. -/
def supportedCrepBudget (program : Prog (RiscV.Word 64)) (n : Nat) : Nat :=
  let body := progToHOL (panSimpProg program)
  let weight := CrepSteps.statementWeight (supportedCallee body)
  3 + weight * (n + 2 + weight)

/-- The counted source run reaches the actual generated Loop entry. Its
extra clock and visit bounds are calculated from the generated code. -/
theorem supported_counted_loop (arch : AsmArchitecture)
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (fuel count n : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (word : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL program)).structs []
      (executableState (progToHOL program)).baseAddress (executableState (progToHOL program)).topAddress
      panSemBitVec64BytesInWord fuel (executableState (progToHOL program)).locals
      (executableState (progToHOL program)).globals (executableState (progToHOL program)).memory
      (executableState (progToHOL program)).ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL program)))) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count)) (countBound : count ≤ n)
    (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact
      (crepStateFrom (panSimpSourceState program (clockedFixtureSource program (n+1))) (progToHOL (panSimpProg program))).memory memory
      (crepStateFrom (panSimpSourceState program (clockedFixtureSource program (n+1))) (progToHOL (panSimpProg program))).memaddrs) :
    let simple := panSimpProg program
    let body := progToHOL simple
    let source := panSimpSourceState program (clockedFixtureSource program (n+1))
    let crep := crepStateFrom source body
    let target := {(loopStateFrom arch source body) with memory := memory}
    let ctxt := witnessLoopContext arch body
    let code := compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln (supportedCallee body)
    let limit := supportedCrepBudget program n
    let budget := 3*loopVisitWeight (optimiseHOL code)*(limit+1)
    ∃ final post,
      evalCrepSemHOLProgExact crep (.seq .skip (.call none (entryName body) [])) =
        (some (.return [.word word]),final) ∧
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms body) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+budget} = (some (.result [.word word]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+budget} ≤
        loopVisitWeight (optimiseHOL code)*(limit+budget+1)+8 ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      crepToLoopMemRelHOLExact final.memory post.memory final.memaddrs ∧
      crepToLoopGlobalsRelHOLExact final.globals post.globals ∧
      crepToLoopCodeRelExact ctxt final.code post.code := by
  let simple := panSimpProg program
  let body := progToHOL simple
  let source := panSimpSourceState program (clockedFixtureSource program (n+1))
  obtain ⟨final,crepRun,crepBound⟩ := fixture_counted_span program supported context primitive handler fuel count (n+1)
    postLocals postGlobals postMemory postFfi word run (by omega)
  have scalar := (supported_panSimp program supported).1
  have nonzero : (crepStateFrom source body).clock ≠ 0 := by
    simp [source,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,panSimpSourceState,clockedFixtureSource,
      loweredStateFrom,PanToCrepSteps.noGlobalsLoweredPreCall]
  have bound : CrepSteps.steps (.seq .skip (.call none (entryName body) [])) (crepStateFrom source body) ≤
      supportedCrepBudget program n := by
    simpa [supportedCrepBudget,supportedCallee,body,simple,source,Nat.add_assoc] using crepBound
  obtain ⟨post,entry,loopRun,visits,state,mem,globals,codeRel⟩ :=
    supported_entry_loop arch simple scalar source final [.word word] (supportedCrepBudget program n)
      memory memoryRel nonzero crepRun bound
  exact ⟨final,post,crepRun,entry,by simpa [wlabWlocExact] using loopRun,visits,state,mem,globals,codeRel⟩

end SteppedFlapjack.Concrete
