import SteppedFlapjack.CrepToLoopSteps.GlobalFrontendSpan
import SteppedFlapjack.Concrete.WordStarter
import SteppedFlapjack.LoopToWordSteps.WholeWordSpan
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps

/-- A lowered Pancake run reaches the generated optimized Word entry at
    an explicit visit- and code-derived bound. -/
theorem callFrontend_word_with_steps {C σ : Type}
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
    (arch : AsmArchitecture) (ref ctxt : CrepToLoopContextExact) (live : NumSet)
    (liveEmpty : live = .ln) (ctxtVars : ctxt.vars = HolFiniteMapExact.empty)
    (crepGlobals : crep.globals = HolFiniteMapExact.empty) (crepLocals : crep.locals = HolFiniteMapExact.empty)
    (memory : BitVec 64 → WordLocW 64) (memRel : crepToLoopMemRelHOLExact crep.memory memory crep.memaddrs)
    (codeRel : crepToLoopCodeRelExact ctxt crep.code (sptFromAList (compileProgHOLExact arch programs)))
    (heapLength : BitVec 64) (heap : crep.topAddr = crep.baseAddr + 2 * heapLength)
    (template : WordSemStateFiniteExact 64 C σ) (start frame : Nat)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (entry : let body := compileProgExactHOLW panCtxt (p)
      (start,[],optimiseHOL (compileHOLExact ctxt live body)) ∈ compileProgHOLExact arch programs) :
    let body := compileProgExactHOLW panCtxt (p)
    let loop := {(concreteDeclLoopState arch crep programs) with memory := memory}
    let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
    let extra := callClockFactor ref (programs.map (fun row => (row.2.1,row.2.2))) crep.clock body * (crepLimit+1)
    let factor := max (callSyntaxCost ref body) (loopCodeWeight loop.code+2)
    let loopLimit := callSyntaxCost ref body + factor * (crep.clock+extra)
    let optimized := optimiseHOL (compileHOLExact ctxt live body)
    let optLimit := loopVisitWeight optimized + max (loopVisitWeight optimized) (loopCodeWeight loop.code+2) * (2*loopLimit)
    let starter := {(phase3Starter arch {crep with clock := crep.clock+extra} programs template heapLength start frame) with memory := memory}
    let raw := loopToWordCompileHOL (compileProgHOLExact arch programs)
    ∃ wordFinal,
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        {starter with clock := 6*optLimit+1, code := sptFromAList (compile wc ac raw).2} =
          (some (.result (.loc 1 0) [.word value]),wordFinal) ∧
      SteppedFlapjack.WordSteps.steps (.call none (some start) [0] none)
        {starter with clock := 6*optLimit+1, code := sptFromAList (compile wc ac raw).2} ≤
          1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac raw).2)) * (6*optLimit+1) ∧
      sourceFinal.ffi = wordFinal.ffi := by
  let body := compileProgExactHOLW panCtxt (p)
  let loop := {(concreteDeclLoopState arch crep programs) with memory := memory}
  let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
  let extra := callClockFactor ref (programs.map (fun row => (row.2.1,row.2.2))) crep.clock body * (crepLimit+1)
  let factor := max (callSyntaxCost ref body) (loopCodeWeight loop.code+2)
  let loopLimit := callSyntaxCost ref body + factor * (crep.clock+extra)
  let optimized := optimiseHOL (compileHOLExact ctxt live body)
  let optLimit := loopVisitWeight optimized + max (loopVisitWeight optimized) (loopCodeWeight loop.code+2) * (2*loopLimit)
  let clocked := {crep with clock := crep.clock+extra}
  let starter := {(phase3Starter arch clocked programs template heapLength start frame) with memory := memory}
  let raw := loopToWordCompileHOL (compileProgHOLExact arch programs)
  let wordCtxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL (sptDifference (accVarsHOL optimized .ln) (LoopToWord.toNumSetHOL []))) .ln
  have relations := concreteDecl_crepLoop_relations arch crep programs crepGlobals
  have loopStateRel : crepToLoopStateRelExact crep loop := by simpa [loop,crepToLoopStateRelExact] using relations.1
  have loopGlobalsRel : crepToLoopGlobalsRelHOLExact crep.globals loop.globals := by simpa [loop] using relations.2.2
  have loopTable : LoopTableSupported loop.code := callFrontend_compiled_loopTableSupported arch programs sources
  have crepLoopLocals : crepToLoopLocalsRelExact ctxt live crep.locals loop.locals := by
    rw [crepLocals,liveEmpty]
    exact empty_crepLoop_locals ctxt loop.locals ctxtVars
  obtain ⟨crepFinal,loopFinal,crepRun,loopRun,loopSteps,loopRel,ffiRel,optRun,optSteps⟩ :=
    callFrontend_loop_with_steps panCtxt p shape source sourceFinal value crep programs sourceLimit
      compiledTable targetTable run sourceBound panCrepRel panCodeRel excpRel panLocalsRel sources
      ref ctxt live loop loopStateRel memRel loopGlobalsRel (by simpa [loop,concreteDeclLoopState] using codeRel)
      loopTable crepLoopLocals
  have clockedHeap : clocked.topAddr = clocked.baseAddr + 2 * heapLength := heap
  have starterRel := phase3Starter_relations arch clocked programs template heapLength start frame memory clockedHeap
  have starterLocals := phase3Starter_locals arch clocked programs template heapLength start frame optimized memory
  have loopEq : {(concreteDeclLoopState arch clocked programs) with memory := memory} = {loop with clock := loop.clock+extra} := by
    simp [loop,clocked,concreteDeclLoopState]
  rw [loopEq] at starterRel starterLocals
  have bodyShape : SimpleLoopSequenceSource optimized := optimise_simpleSequence
    (callFrontend_compiled_loopShape shape ctxt live)
  have wordEntry : (start,1,(LoopToWord.compHOL wordCtxt optimized (start,2)).1) ∈ raw := by
    apply List.mem_map.mpr
    exact ⟨(start,[],optimized),entry,by simp [loopToWordCompFuncHOL,wordCtxt]⟩
  have wordUnique : (raw.map Prod.fst).Nodup := by
    simpa [raw,loopToWordCompileHOL,loopToWordCompileProgHOL,List.map_map,Function.comp_def] using
      firstCompileProgAllDistinctExact arch programs
  have span := loopTable_wholeWord_span bodyShape {loop with clock := loop.clock+extra} loopFinal
    (some (.result [.word value])) (by simpa using loopTable) start starter wordCtxt (start,2) optLimit raw wc ac
    wordEntry wordUnique (loopToWord_programSafety _) (by rfl) starterRel.2.1 starterRel.2.2.1 starterRel.2.2.2
    ⟨optRun,by simp,starterRel.1,by simpa [wordCtxt] using starterLocals.1,starterLocals.2.1,Or.inr rfl,by decide,
      by simpa [wordCtxt] using starterLocals.2.2⟩ (.return _) optSteps
  obtain ⟨wordPost,wordResult,resultRel,success,wordFfi,wordSteps⟩ := span
  have resultEq : wordResult = some (.result (.loc 1 0) [.word value]) := resultRel.2.1
  refine ⟨(WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
    {starter with clock := 6*optLimit+1, code := sptFromAList (compile wc ac raw).2}).2,?_,wordSteps,?_⟩
  · apply Prod.ext
    · exact success.trans resultEq
    · rfl
  · exact ffiRel.trans wordFfi.symm
/-- Global lowering feeds the shared lowered-Pancake-to-Word span. -/
theorem globalCallFrontend_word_with_steps {C σ : Type}
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
    (arch : AsmArchitecture) (ref ctxt : CrepToLoopContextExact) (live : NumSet)
    (liveEmpty : live = .ln) (ctxtVars : ctxt.vars = HolFiniteMapExact.empty)
    (crepGlobals : crep.globals = HolFiniteMapExact.empty) (crepLocals : crep.locals = HolFiniteMapExact.empty)
    (memory : BitVec 64 → WordLocW 64) (memRel : crepToLoopMemRelHOLExact crep.memory memory crep.memaddrs)
    (codeRel : crepToLoopCodeRelExact ctxt crep.code (sptFromAList (compileProgHOLExact arch programs)))
    (heapLength : BitVec 64) (heap : crep.topAddr = crep.baseAddr + 2 * heapLength)
    (template : WordSemStateFiniteExact 64 C σ) (start frame : Nat)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (entry : let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
      (start,[],optimiseHOL (compileHOLExact ctxt live body)) ∈ compileProgHOLExact arch programs) :
    let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
    let loop := {(concreteDeclLoopState arch crep programs) with memory := memory}
    let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
    let extra := callClockFactor ref (programs.map (fun row => (row.2.1,row.2.2))) crep.clock body * (crepLimit+1)
    let factor := max (callSyntaxCost ref body) (loopCodeWeight loop.code+2)
    let loopLimit := callSyntaxCost ref body + factor * (crep.clock+extra)
    let optimized := optimiseHOL (compileHOLExact ctxt live body)
    let optLimit := loopVisitWeight optimized + max (loopVisitWeight optimized) (loopCodeWeight loop.code+2) * (2*loopLimit)
    let starter := {(phase3Starter arch {crep with clock := crep.clock+extra} programs template heapLength start frame) with memory := memory}
    let raw := loopToWordCompileHOL (compileProgHOLExact arch programs)
    ∃ wordFinal,
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        {starter with clock := 6*optLimit+1, code := sptFromAList (compile wc ac raw).2} =
          (some (.result (.loc 1 0) [.word value]),wordFinal) ∧
      SteppedFlapjack.WordSteps.steps (.call none (some start) [0] none)
        {starter with clock := 6*optLimit+1, code := sptFromAList (compile wc ac raw).2} ≤
          1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac raw).2)) * (6*optLimit+1) ∧
      sourceFinal.ffi = wordFinal.ffi := by
  obtain ⟨panFinal,panRun,panRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    p source (some (.returned (.val (.word value)))) globals panTarget sourceFinal ⟨globalRel,run,by simp⟩
  have visitEq := globalCallFrontend_controlSteps shape source sourceFinal panTarget
    (some (.returned (.val (.word value)))) sourceTable run (by simp) globalRel
  have targetBound : controlSteps (compileProgExactHOL globals p) panTarget ≤ sourceLimit := by
    rw [visitEq]
    exact sourceBound
  obtain ⟨wordFinal,wordRun,wordSteps,ffi⟩ :=
    callFrontend_word_with_steps panCtxt (compileProgExactHOL globals p) (globalCallFrontend_compiled shape)
      panTarget panFinal value crep programs sourceLimit compiledTable targetTable panRun targetBound
      panCrepRel panCodeRel excpRel panLocalsRel sources arch ref ctxt live liveEmpty ctxtVars crepGlobals crepLocals
      memory memRel codeRel heapLength heap template start frame wc ac entry
  rcases panRel with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,panFfi,_⟩
  exact ⟨wordFinal,wordRun,wordSteps,panFfi.trans ffi⟩

end SteppedFlapjack.LoopToWordSteps
