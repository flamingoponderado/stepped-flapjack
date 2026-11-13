import SteppedFlapjack.PanToCrepSteps.GlobalFrontendControl
import SteppedFlapjack.CrepToLoopSteps.CallFrontendShape
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The optimizer bound also applies when the entry body is not looked up in
    the code table, by including its own weight in the concrete factor. -/
private theorem optimise_source_bound_max {F : Type} {p : HolLoopProg 64}
    (shape : SimpleLoopSequenceSource p) (s post : LoopSemStateFiniteExact 64 F)
    (result : Option (LoopResultExact 64)) (code : LoopTableSupported s.code)
    (run : evaluate p s = (result,post)) (complete : CompleteLoopResult result) :
    evaluate (optimiseHOL p) s = (result,post) ∧
    SteppedFlapjack.LoopSteps.steps (optimiseHOL p) s ≤ loopVisitWeight (optimiseHOL p) +
      max (loopVisitWeight (optimiseHOL p)) (loopCodeWeight s.code + 2) * (2 * SteppedFlapjack.LoopSteps.steps p s) := by
  have optRun : evaluate (optimiseHOL p) s = (result,post) := by
    apply optimise_correct p s result post
    refine ⟨run,?_,?_,?_,?_⟩ <;> cases complete <;> simp_all
  let K := max (loopVisitWeight (optimiseHOL p)) (loopCodeWeight s.code+2)
  have optBound := simpleSequence_global_bound (optimiseHOL p) s K (optimise_simpleSequence shape) code
    (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have consumed := simpleSequence_global_consumed p s shape code
  rw [optRun] at optBound
  rw [run] at consumed
  exact ⟨optRun, optBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ consumed) _)⟩

/-- A successful lowered Pancake run reaches Loop at a bound computed
    from its visits and the actual generated program and code table. -/
theorem callFrontend_loop_with_steps {σ : Type}
    (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : CallFrontend panCtxt p)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (value : BitVec 64)
    (crep : CrepSemHOLState 64 σ) (programs : List (MlS × List Nat × CrepProgHOL 64)) (sourceLimit : Nat)
    (compiledTable : crep.code = alistToFmapCodeExact programs) (targetTable : CallFrontendCode panCtxt source.code)
    (run : source.evaluateHOLFiniteState p = (some (.returned (.val (.word value))),sourceFinal))
    (sourceBound : controlSteps p source ≤ sourceLimit)
    (panCrepRel : panToCrepStateRelFiniteExact source crep)
    (panCodeRel : codeRelExactHOLW panCtxt source.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact panCtxt.eids source.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact panCtxt source.locals crep.locals)
    (sources : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (ref ctxt : CrepToLoopContextExact) (live : NumSet) (loop : LoopSemStateFiniteExact 64 σ)
    (stateRel : crepToLoopStateRelExact crep loop)
    (memRel : crepToLoopMemRelHOLExact crep.memory loop.memory crep.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact crep.globals loop.globals)
    (codeRel : crepToLoopCodeRelExact ctxt crep.code loop.code) (loopTable : LoopTableSupported loop.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live crep.locals loop.locals) :
    let lowered := p
    let body := compileProgExactHOLW panCtxt lowered
    let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let extra := callClockFactor ref rows crep.clock body * (crepLimit+1)
    let factor := max (callSyntaxCost ref body) (loopCodeWeight loop.code+2)
    ∃ crepFinal loopFinal,
      evalCrepSemHOLProgExact crep body = (some (.return [.word value]),crepFinal) ∧
      evaluate (compileHOLExact ctxt live body) {loop with clock := loop.clock+extra} =
        (some (.result [.word value]),loopFinal) ∧
      SteppedFlapjack.LoopSteps.steps (compileHOLExact ctxt live body) {loop with clock := loop.clock+extra} ≤
        callSyntaxCost ref body + factor * (crep.clock+extra) ∧
      crepToLoopStateRelExact crepFinal {loopFinal with clock := crepFinal.clock} ∧
      sourceFinal.ffi = loopFinal.ffi ∧
      evaluate (optimiseHOL (compileHOLExact ctxt live body)) {loop with clock := loop.clock+extra} =
        (some (.result [.word value]),loopFinal) ∧
      SteppedFlapjack.LoopSteps.steps (optimiseHOL (compileHOLExact ctxt live body)) {loop with clock := loop.clock+extra} ≤
        loopVisitWeight (optimiseHOL (compileHOLExact ctxt live body)) +
          max (loopVisitWeight (optimiseHOL (compileHOLExact ctxt live body))) (loopCodeWeight loop.code+2) *
            (2 * (callSyntaxCost ref body + factor * (crep.clock+extra))) := by
  let lowered := p
  let body := compileProgExactHOLW panCtxt lowered
  let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
  have bound := callFrontend_compiled_steps panCtxt p shape source sourceFinal
    (some (.returned (.val (.word value)))) crep programs compiledTable targetTable run (by simp)
    panCrepRel panCodeRel excpRel panLocalsRel
  have crepBound : SteppedFlapjack.CrepSteps.steps body crep ≤ crepLimit :=
    bound.trans (Nat.mul_le_mul_left _ sourceBound)
  have correct : pcCompileCorrectAt p source :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨crepResult,crepFinal,crepRun,crepRel,_,_,resultRel⟩ :=
    correct _ sourceFinal crep panCtxt run (by simp) panCrepRel panCodeRel excpRel panLocalsRel (callFrontend_localised shape)
  have resultEq : crepResult = some (.return [.word value]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst crepResult
  simp only [flattenHOL] at crepRun
  obtain ⟨loopFinal,loopRun,steps,rel,_,_,_,_⟩ := callFrontend_wholeVisits_explicit panCtxt lowered
    shape programs sources ref ctxt live crep crepFinal (some (.return [.word value])) loop
    compiledTable crepRun (by simp) (by simp) crepLimit crepBound stateRel memRel globalsRel codeRel loopTable localsRel
  have loopRun' : evaluate (compileHOLExact ctxt live body)
      {loop with clock := loop.clock + callClockFactor ref (programs.map (fun row => (row.2.1,row.2.2))) crep.clock body * (crepLimit+1)} =
        (some (.result [.word value]),loopFinal) := by
    simpa [resultToLoop,wlabWlocExact] using loopRun
  have loopShape := callFrontend_compiled_loopShape shape ctxt live
  have optimized := optimise_source_bound_max loopShape _ loopFinal (some (.result [.word value]))
    (by simpa using loopTable) loopRun' (.return _)
  have optimizedSteps := optimized.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 steps)) _)
  rcases crepRel with ⟨_,_,_,_,_,_,_,crepFfi,_,_⟩
  have loopFfi : crepFinal.ffi = loopFinal.ffi := rel.2.2.2.2.1
  exact ⟨crepFinal,loopFinal,crepRun,loopRun',steps,rel,crepFfi.trans loopFfi,optimized.1,optimizedSteps⟩
/-- Global lowering feeds the shared lowered-Pancake-to-Loop span. -/
theorem globalCallFrontend_loop_with_steps {σ : Type}
    (globals : PanGlobalsContextExact 64) (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : GlobalCallFrontend globals panCtxt p)
    (source sourceFinal panTarget : PanSemStateFiniteExact 64 σ) (value : BitVec 64)
    (crep : CrepSemHOLState 64 σ) (programs : List (MlS × List Nat × CrepProgHOL 64)) (sourceLimit : Nat)
    (sourceTable : GlobalCallTable globals source.code)
    (compiledTable : crep.code = alistToFmapCodeExact programs) (targetTable : CallFrontendCode panCtxt panTarget.code)
    (run : source.evaluateHOLFiniteState p = (some (.returned (.val (.word value))),sourceFinal))
    (sourceBound : controlSteps p source ≤ sourceLimit)
    (globalRel : panGlobalsStateRelHOLExact true globals source panTarget)
    (panCrepRel : panToCrepStateRelFiniteExact panTarget crep)
    (panCodeRel : codeRelExactHOLW panCtxt panTarget.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact panCtxt.eids panTarget.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact panCtxt panTarget.locals crep.locals)
    (sources : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (ref ctxt : CrepToLoopContextExact) (live : NumSet) (loop : LoopSemStateFiniteExact 64 σ)
    (stateRel : crepToLoopStateRelExact crep loop)
    (memRel : crepToLoopMemRelHOLExact crep.memory loop.memory crep.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact crep.globals loop.globals)
    (codeRel : crepToLoopCodeRelExact ctxt crep.code loop.code) (loopTable : LoopTableSupported loop.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live crep.locals loop.locals) :
    let lowered := compileProgExactHOL globals p
    let body := compileProgExactHOLW panCtxt lowered
    let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let extra := callClockFactor ref rows crep.clock body * (crepLimit+1)
    let factor := max (callSyntaxCost ref body) (loopCodeWeight loop.code+2)
    ∃ crepFinal loopFinal,
      evalCrepSemHOLProgExact crep body = (some (.return [.word value]),crepFinal) ∧
      evaluate (compileHOLExact ctxt live body) {loop with clock := loop.clock+extra} =
        (some (.result [.word value]),loopFinal) ∧
      SteppedFlapjack.LoopSteps.steps (compileHOLExact ctxt live body) {loop with clock := loop.clock+extra} ≤
        callSyntaxCost ref body + factor * (crep.clock+extra) ∧
      crepToLoopStateRelExact crepFinal {loopFinal with clock := crepFinal.clock} ∧
      sourceFinal.ffi = loopFinal.ffi ∧
      evaluate (optimiseHOL (compileHOLExact ctxt live body)) {loop with clock := loop.clock+extra} =
        (some (.result [.word value]),loopFinal) ∧
      SteppedFlapjack.LoopSteps.steps (optimiseHOL (compileHOLExact ctxt live body)) {loop with clock := loop.clock+extra} ≤
        loopVisitWeight (optimiseHOL (compileHOLExact ctxt live body)) +
          max (loopVisitWeight (optimiseHOL (compileHOLExact ctxt live body))) (loopCodeWeight loop.code+2) *
            (2 * (callSyntaxCost ref body + factor * (crep.clock+extra))) := by
  obtain ⟨panFinal,panRun,panRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    p source (some (.returned (.val (.word value)))) globals panTarget sourceFinal ⟨globalRel,run,by simp⟩
  have visitEq := globalCallFrontend_controlSteps shape source sourceFinal panTarget
    (some (.returned (.val (.word value)))) sourceTable run (by simp) globalRel
  have targetBound : controlSteps (compileProgExactHOL globals p) panTarget ≤ sourceLimit := by
    rw [visitEq]
    exact sourceBound
  obtain ⟨crepFinal,loopFinal,crepRun,loopRun,steps,rel,ffi,optRun,optSteps⟩ :=
    callFrontend_loop_with_steps panCtxt (compileProgExactHOL globals p) (globalCallFrontend_compiled shape)
      panTarget panFinal value crep programs sourceLimit compiledTable targetTable panRun targetBound
      panCrepRel panCodeRel excpRel panLocalsRel sources ref ctxt live loop stateRel memRel globalsRel codeRel loopTable localsRel
  rcases panRel with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,panFfi,_⟩
  exact ⟨crepFinal,loopFinal,crepRun,loopRun,steps,rel,panFfi.trans ffi,optRun,optSteps⟩

end SteppedFlapjack.CrepToLoopSteps
