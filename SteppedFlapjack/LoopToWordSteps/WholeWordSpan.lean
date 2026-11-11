import SteppedFlapjack.WordAllocSteps.WholeTailCode
import SteppedFlapjack.LoopToWordSteps.WholeCallProgram
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.PanLang Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LoopLiveSteps
variable {C F : Type}
/-- A normalized function-body run lifts to the actual optimized start call. -/
theorem normalizedBody_optimizedStart
    (body : WordLangProgHOL (BitVec 64)) (start ticks : Nat)
    (starter post : WordSemStateFiniteExact 64 C F) (result : Option (WordSemResult 64))
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (wc : Config) (ac : AsmConfigExact 64)
    (entryMember : (start,1,body) ∈ programs) (nodup : (programs.map Prod.fst).Nodup)
    (safety : WordProgramSafety programs) (code : starter.code = sptFromAList programs)
    (arg : getVar 0 starter = some (.loc 1 0)) (stack : starter.stack = [])
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk starter.gcFun)
    (goodResult : wordSemBadFunReturn result = false) (notError : result ≠ some .error)
    (run : let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
      evaluate body {word with clock := ticks} = (result,post)) :
    let final := evaluate (.call none (some start) [0] none)
      {starter with clock := ticks+1, code := sptFromAList (compile wc ac programs).2}
    final.1 = result ∧ final.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some start) [0] none)
        {starter with clock := ticks+1, code := sptFromAList (compile wc ac programs).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac programs).2)) * (ticks+1) := by
  let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
  have entryLookup := (wholeCompile_entry_lookups wc ac programs start 1 body entryMember nodup).1
  have arg0 : getVar 0 {starter with clock := ticks+1} = some (.loc 1 0) := arg
  have args : getVars [0] {starter with clock := ticks+1} = some [(.loc 1 0 : WordLocW 64)] := by
    simp [WordSemStateFiniteExact.getVars,arg0]
  have wordFind : wordSemFindCode (some start) [(.loc 1 0 : WordLocW 64)]
      starter.code starter.stackSize = some ([.loc 1 0],body,sptLookup start starter.stackSize) := by
    simp [wordSemFindCode,code,entryLookup]
  have unoptimizedRun : evaluate (.call none (some start) [0] none) {starter with clock := ticks+1} =
      (result,post) := by
    rw [WordSemStateFiniteExact.evaluate]
    simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,wordFind]
    simp only [show ticks+1 ≠ 0 by omega,↓reduceDIte]
    have h : callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize)
        (decClock {starter with clock := ticks+1}) = {word with clock := ticks} := by
      simp [word,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]
    rw [h,run]
    simp [goodResult]
  have nonerror : (evaluate (.call none (some start) [0] none) {starter with clock := ticks+1}).1 ≠ some .error := by
    rw [unoptimizedRun]
    exact notError
  have target := wholeCompile_start_agrees wc ac programs safety starter start (ticks+1) code gc stack nonerror
  refine ⟨?_,?_,?_⟩
  · simpa [unoptimizedRun] using target.1
  · simpa [unoptimizedRun] using target.2.1
  · have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
    rw [compileWith_eq_compile _ allocator]
    exact target.2.2

/-- A complete Loop run with calls throughout its function table reaches the
actual optimized Word start call, with an explicit output-table visit bound. -/
theorem loopTable_wholeWord_span {p : HolLoopProg 64}
    (shape : SimpleLoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (table : LoopTableSupported source.code)
    (start : Nat) (starter : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (limit : Nat) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wc : Config) (ac : AsmConfigExact 64)
    (entryMember : (start,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup) (safety : WordProgramSafety programs)
    (code : starter.code = sptFromAList programs)
    (arg : getVar 0 starter = some (.loc 1 0)) (stack : starter.stack = [])
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk starter.gcFun)
    (premises : let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
      evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit) :
    let final := evaluate (.call none (some start) [0] none)
      {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac programs).2}
    ∃ wordPost wordResult,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0)
        (callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter))
        result sourcePost wordResult wordPost ∧
      final.1 = wordResult ∧ final.2.ffi = sourcePost.ffi ∧
      WordSteps.steps (.call none (some start) [0] none)
        {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac programs).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac programs).2)) * (6*limit+1) := by
  let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopTable_correct_with_steps p source shape table result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨wordComplete,notError,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have wordNoMt : WordProps.noMtCode word.code := by simpa [word,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,code] using safety.2.1
  have wordNoInstall : WordProps.noInstallCode word.code := by simpa [word,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,code] using safety.1
  have normalized := WordToStackSteps.tableWord_normalized_run _ word wordPost wordResult (6*limit)
    (loopComp_noMt p ctxt labels) (loopComp_noInstall p ctxt labels) wordNoMt wordNoInstall wordRun notTimeout
      (wordBound.trans (Nat.mul_le_mul_left 6 sourceBound))
  have goodResult : wordSemBadFunReturn wordResult = false := by cases wordComplete <;> rfl
  have startRun := normalizedBody_optimizedStart (LoopToWord.compHOL ctxt p labels).1 start (6*limit)
    starter {wordPost with clock := 6*limit-(word.clock-wordPost.clock)} wordResult programs wc ac
    entryMember nodup safety code arg stack gc goodResult notError normalized
  exact ⟨wordPost,wordResult,wordRel,startRun.1,by simpa [wordFfi] using startRun.2.1,startRun.2.2⟩


theorem callFrontend_declaration_optimizedStart {C σ : Type}
    (declarations : List (DeclHOL 64))
    (unique : ((functionsHOL declarations).map Prod.fst).Nodup)
    (noInline : (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1)
    (program : ProgHOL 64)
    (shape : CallFrontend (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)) program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (value : BitVec 64)
    (code : source.code = HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (noExceptions : getEidsFromDeclsHOL declarations = HolFiniteMapExact.empty)
    (run : source.evaluateHOLFiniteState program = (some (.returned (.val (.word value))),sourceFinal))
    (sourceLimit : Nat) (sourceBound : controlSteps program source ≤ sourceLimit)
    (arch : AsmArchitecture) (start : Flapjack.Basis.Pure.MlString.MlString) (entry : CrepProgHOL 64)
    (found : holAlookup (compileProgDeclsHOLW declarations) start = some ([],entry))
    (ref : CrepToLoopContextExact) (live : NumSet) (loop : LoopSemStateFiniteExact 64 σ)
    (loopCode : loop.code = sptFromAList (compileProgHOLExact arch (compileProgDeclsHOLW declarations)))
    (stateRel : crepToLoopStateRelExact (concreteDeclCrepState source (compileProgDeclsHOLW declarations)) loop)
    (memRel : crepToLoopMemRelHOLExact (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).memory
      loop.memory (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).globals loop.globals)
    (localsRel : crepToLoopLocalsRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW declarations)) 0)
      live (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).locals loop.locals)
    (starter : WordSemStateFiniteExact 64 C σ) (entryLoc : Nat) (wordCtxt : Spt Nat) (label : Nat × Nat)
    (wc : Config) (ac : AsmConfigExact 64)
    (starterCode : starter.code = sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW declarations))))
    (arg : getVar 0 starter = some (.loc 1 0)) (stack : starter.stack = [])
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk starter.gcFun)
    (entryMember : let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0 (getEidsFromDeclsHOL declarations)
      let programs := compileProgDeclsHOLW declarations
      let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
      let body := (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (compileProgExactHOLW panCtxt program)) label).1
      (entryLoc,1,body) ∈ loopToWordCompileHOL (compileProgHOLExact arch programs))
    (wordRel : let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0 (getEidsFromDeclsHOL declarations)
      let programs := compileProgDeclsHOLW declarations
      let crep := compileProgExactHOLW panCtxt program
      let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * sourceLimit
      let rows := programs.map (fun row => (row.2.1,row.2.2))
      let budget := callClockFactor ref rows source.clock crep * (limit+1)
      let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup entryLoc starter.stackSize) (decClock starter)
      loopToWordStateRelHOLExact {loop with clock := loop.clock+budget} word)
    (wordLocals : LoopToWord.localsRelHOL wordCtxt loop.locals
      (callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup entryLoc starter.stackSize) (decClock starter)).locals)
    (acc : ∀ k, sptMem k (accVarsHOL (compileHOLExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW declarations)) 0) live
      (compileProgExactHOLW (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
        (getEidsFromDeclsHOL declarations)) program)) .ln) → sptMem k wordCtxt) :
    let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)
    let programs := compileProgDeclsHOLW declarations
    let crep := compileProgExactHOLW panCtxt program
    let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * sourceLimit
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let budget := callClockFactor ref rows source.clock crep * (limit+1)
    let factor := max (callSyntaxCost ref crep) (loopCodeWeight loop.code+2)
    let ticks := 6 * (callSyntaxCost ref crep + factor * (source.clock+budget))
    let rawWords := loopToWordCompileHOL (compileProgHOLExact arch programs)
    ∃ final, evaluate (.call none (some entryLoc) [0] none)
        {starter with clock := ticks+1, code := sptFromAList (compile wc ac rawWords).2} =
          (some (.result (.loc 1 0) [.word value]),final) ∧
      final.ffi = sourceFinal.ffi ∧
      WordSteps.steps (.call none (some entryLoc) [0] none)
        {starter with clock := ticks+1, code := sptFromAList (compile wc ac rawWords).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac rawWords).2)) * (ticks+1) := by
  let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup entryLoc starter.stackSize) (decClock starter)
  have codeWord : word.code = sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW declarations))) := by
    simpa [word,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock] using starterCode
  have retLookup : sptLookup 0 word.locals = some (.loc 1 0) := by
    change sptLookup 0 (sptFromList2 [(.loc 1 0 : WordLocW 64)]) = _
    with_unfolding_all rfl
  obtain ⟨crepFinal,loopFinal,wordFinal,_,_,_,normalized,_,ffi⟩ :=
    callFrontend_declaration_word_explicit declarations unique noInline shapes program shape source sourceFinal value
      code locals globals structs exceptions noExceptions run sourceLimit sourceBound arch start entry found ref live loop
      loopCode stateRel memRel globalsRel localsRel word wordCtxt (.loc 1 0) label codeWord wordRel wordLocals
      retLookup (by decide) acc
  let programs := compileProgDeclsHOLW declarations
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
    (getEidsFromDeclsHOL declarations)
  let crep := compileProgExactHOLW panCtxt program
  let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * sourceLimit
  let rows := programs.map (fun row => (row.2.1,row.2.2))
  let budget := callClockFactor ref rows source.clock crep * (limit+1)
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let body := (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live crep) label).1
  let factor := max (callSyntaxCost ref crep) (loopCodeWeight loop.code+2)
  let ticks := 6 * (callSyntaxCost ref crep + factor * (source.clock+budget))
  let rawWords := loopToWordCompileHOL (compileProgHOLExact arch programs)
  have names : (rawWords.map Prod.fst).Nodup := by
    apply loopToWordFirstCompileAllDistinct
    exact firstCompileProgAllDistinctExact arch programs
  have normalized' : evaluate body {word with clock := ticks} = (some (.result (.loc 1 0) [.word value]),wordFinal) := by
    simpa [body,ctxt,crep,panCtxt,ticks,factor,budget,rows,limit,programs] using normalized
  have member : (entryLoc,1,body) ∈ rawWords := entryMember
  have result := normalizedBody_optimizedStart body entryLoc ticks starter wordFinal
    (some (.result (.loc 1 0) [.word value])) rawWords wc ac member names
    (loopToWord_programSafety (compileProgHOLExact arch programs)) starterCode arg stack gc (by rfl) (by simp) normalized'
  refine ⟨(evaluate (.call none (some entryLoc) [0] none)
    {starter with clock := ticks+1,code := sptFromAList (compile wc ac rawWords).2}).2,?_,?_,?_⟩
  · exact Prod.ext result.1 rfl
  · exact result.2.1.trans ffi
  · exact result.2.2

end SteppedFlapjack.LoopToWordSteps
