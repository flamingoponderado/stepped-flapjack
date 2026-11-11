import SteppedFlapjack.LoopToWordSteps.TailCall
import SteppedFlapjack.LoopToWordSteps.StackReady
import SteppedFlapjack.WordToStackSteps.NormalizedClock
import SteppedFlapjack.LoopLiveSteps.TailEntryGlobalBound
import SteppedFlapjack.CrepToLoopSteps.CallFrontendShape
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopSteps

private theorem tail_dispatch {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args : List Nat) (s : LoopSemStateFiniteExact width F)
    (bodyProp : ∀ vals env body, getVars args s = some vals →
      findCode (some loc) vals s.code = some (env,body) → s.clock ≠ 0 →
      SixBoundPropertyAt C body {decClock s with locals := env}) :
    SixBoundPropertyAt C (.call none (some loc) args none) s := by
  cases get : getVars args s with
  | none =>
    intro res final target ctxt retv labels premises
    have run := premises.1
    rw [evaluate] at run
    simp only [get,Prod.mk.injEq] at run
    exact False.elim (premises.2.1 run.1.symm)
  | some vals =>
    cases found : findCode (some loc) vals s.code with
    | none =>
      intro res final target ctxt retv labels premises
      have run := premises.1
      rw [evaluate] at run
      simp only [get,found,Prod.mk.injEq] at run
      exact False.elim (premises.2.1 run.1.symm)
    | some pair =>
      obtain ⟨env,body⟩ := pair
      exact sixBoundedDirectTail loc args vals env body s (bodyProp vals env body get found) get found

private theorem returning_dispatch {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (markHandler markNormal : Bool) (s : LoopSemStateFiniteExact width F)
    (bodyProp : ∀ vals env body cut, getVars args s = some vals →
      findCode (some loc) vals s.code = some (env,body) →
      cutRes live (none,s) = (none,cut) → SixBoundPropertyAt C body {cut with locals := env}) :
    SixBoundPropertyAt C (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s := by
  cases get : getVars args s with
  | none =>
    intro res final target ctxt retv labels premises
    have run := premises.1
    rw [evaluate] at run
    simp only [get,Prod.mk.injEq] at run
    exact False.elim (premises.2.1 run.1.symm)
  | some vals =>
    cases found : findCode (some loc) vals s.code with
    | none =>
      intro res final target ctxt retv labels premises
      have run := premises.1
      rw [evaluate] at run
      simp only [get,found,Prod.mk.injEq] at run
      exact False.elim (premises.2.1 run.1.symm)
    | some pair =>
      obtain ⟨env,body⟩ := pair
      by_cases distinct : names.Nodup
      · exact sixBoundedDirectReturning loc args names live liveOut exc markHandler markNormal s vals env body
          get found distinct (fun cut h => bodyProp vals env body cut get found h)
      · intro res final target ctxt retv labels premises
        have run := premises.1
        rw [evaluate] at run
        simp only [get,found,distinct,not_false_eq_true,if_true,Prod.mk.injEq] at run
        exact False.elim (premises.2.1 run.1.symm)
set_option maxHeartbeats 5000000 in
/-- Every supported Loop program has the sixfold Loop-to-Word simulation when
all bodies in its actual code table have the same recursive call-aware shape. -/
theorem loopTable_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (shape : SimpleLoopSequenceSource p) (table : LoopTableSupported s.code) :
    SixBoundPropertyAt C p s := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock,sizeOf p) = x → SimpleLoopSequenceSource p → LoopTableSupported s.code →
      SixBoundPropertyAt C p s := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx shape table
      have ih : ∀ (q : HolLoopProg width) (t : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (t.clock,sizeOf q) (s.clock,sizeOf p) →
          SimpleLoopSequenceSource q → t.code = s.code → SixBoundPropertyAt C q t := by
        intro q t smaller qshape same
        have table' : LoopTableSupported t.code := by rw [same]; exact table
        exact ih0 _ (hx ▸ smaller) q t rfl qshape table'
      clear ih0 hx
      cases shape with
      | branch h => exact loopProgram_correct_with_steps (loopBranch_program h) s
      | @loop live exits body h =>
        apply sixBoundedLoopAt live exits body s
        intro t same smaller
        exact ih body t (Prod.Lex.left _ _ smaller) h same
      | @seq a b ha hb =>
        apply sixBoundedSeq a b s
        refine ⟨?_,ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl⟩
        intro res middle h
        obtain ⟨run,rfl⟩ := h
        have clock := evaluate_clock a s none middle run.symm
        have same := SteppedFlapjack.LoopLiveSteps.evaluate_code a s middle none run.symm
        exact ih b middle (lexLt clock (by simp_wf)) hb same
      | @conditional cmp r ri live a b ha hb =>
        apply sixBoundedIf cmp r ri a b live s
        intro v2 v3 v5 x v13 y branch h1 h2 h3 h4 h5 h6
        cases branch <;> simp only [Bool.false_eq_true,↓reduceIte]
        · exact ih b s (lexLt (Nat.le_refl _) (by simp_wf; omega)) hb rfl
        · exact ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl
      | @mark q h => exact sixBoundedMark q s (ih q s (lexLt (Nat.le_refl _) (by simp_wf)) h rfl)
      | tail loc args =>
        apply tail_dispatch loc args s
        intro vals env body get found nonzero
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body found
        have small : (decClock s).clock < s.clock := by simp [decClock]; omega
        exact ih body {decClock s with locals := env} (Prod.Lex.left _ _ small) (table loc params body lookup) rfl
      | returning names live loc exc args liveOut =>
        apply returning_dispatch loc args names live liveOut exc false false s
        intro vals env body cut get found cutRun
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body found
        have small := cutRes_none_clock cutRun
        have same : cut.code = s.code := by have h := cutRes_code live none s; rw [cutRun] at h; exact h
        exact ih body {cut with locals := env} (Prod.Lex.left _ _ small) (table loc params body lookup) same
      | returningMarked names live loc exc args liveOut =>
        apply returning_dispatch loc args names live liveOut exc true true s
        intro vals env body cut get found cutRun
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body found
        have small := cutRes_none_clock cutRun
        have same : cut.code = s.code := by have h := cutRes_code live none s; rw [cutRun] at h; exact h
        exact ih body {cut with locals := env} (Prod.Lex.left _ _ small) (table loc params body lookup) same
  exact key _ p s rfl shape table

private theorem resultCase_noTimeout {width : Nat} [NeZero width] {C F : Type} (ctxt : Spt Nat) (retv : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (res : Option (LoopResultExact width))
    (post : LoopSemStateFiniteExact width F) (wordResult : Option (WordSemResult width))
    (wordPost : WordSemStateFiniteExact width C F)
    (h : resultCase ctxt retv s res post wordResult wordPost)
    (notTimeout : res ≠ some .timeOut) : wordResult ≠ some .timeOut := by
  cases res with
  | none => simp [resultCase] at h; simp [h.2.1]
  | some r =>
    cases r <;> simp_all [resultCase]
    case exception v =>
      intro ht
      have ne : wordResult ≠ some .error := by rw [ht]; simp
      obtain ⟨a,b,eq⟩ := h.2.1 ne
      rw [ht] at eq
      cases eq

section FrontendBound
open Flapjack.Pancake.PanLang Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps

/-- The concrete frontend and whole-table Loop bounds compose with the sixfold Word simulation. -/
theorem callFrontend_word_explicit {width : Nat} [NeZero width] {C σ : Type}
    (panCtxt : PanToCrepContextExact width) (p : ProgHOL width) (shape : CallFrontend panCtxt p)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact width) (q : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (ref ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (sourceCode : source.code = alistToFmapCodeExact programs)
    (run : evalCrepSemHOLProgExact source (compileProgExactHOLW panCtxt p) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (nonTimeout : result ≠ some .timeOut)
    (sourceLimit : Nat) (sourceBound : CrepSteps.steps (compileProgExactHOLW panCtxt p) source ≤ sourceLimit)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code) (targetTable : LoopTableSupported target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (word : WordSemStateFiniteExact width C σ) (wordCtxt : Spt Nat) (retv : WordLocW width) (label : Nat × Nat)
    (wordTable : List (Nat × List Nat × HolLoopProg width))
    (wordCode : word.code = sptFromAList (loopToWordCompileHOL wordTable))
    (wordRel : let rows := programs.map (fun row => (row.2.1,row.2.2))
      let crep := compileProgExactHOLW panCtxt p
      let budget := callClockFactor ref rows source.clock crep * (sourceLimit+1)
      loopToWordStateRelHOLExact {target with clock := target.clock+budget} word)
    (wordLocals : LoopToWord.localsRelHOL wordCtxt target.locals word.locals)
    (retvLookup : sptLookup 0 word.locals = some retv) (dim : goodDimindex width)
    (notWord : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL (compileHOLExact ctxt live (compileProgExactHOLW panCtxt p)) .ln) → sptMem k wordCtxt) :
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let crep := compileProgExactHOLW panCtxt p
    let loop := compileHOLExact ctxt live crep
    let budget := callClockFactor ref rows source.clock crep * (sourceLimit+1)
    let factor := max (callSyntaxCost ref crep) (loopCodeWeight target.code+2)
    ∃ loopPost wordPost wordResult,
      evaluate loop {target with clock := target.clock+budget} = (resultToLoop result,loopPost) ∧
      LoopSteps.steps loop {target with clock := target.clock+budget} ≤
        callSyntaxCost ref crep + factor * (source.clock+budget) ∧
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL wordCtxt loop label).1 word = (wordResult,wordPost) ∧
      wordPost.ffi = loopPost.ffi ∧ resultCase wordCtxt retv word (resultToLoop result) loopPost wordResult wordPost ∧
      WordSteps.steps (LoopToWord.compHOL wordCtxt loop label).1 word ≤
        6 * (callSyntaxCost ref crep + factor*(source.clock+budget)) ∧
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL wordCtxt loop label).1
        {word with clock := 6 * (callSyntaxCost ref crep + factor*(source.clock+budget))} =
        (wordResult,{wordPost with clock := 6 * (callSyntaxCost ref crep + factor*(source.clock+budget)) -
          (word.clock-wordPost.clock)}) ∧
      crepToLoopStateRelExact sourceFinal {loopPost with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory loopPost.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals loopPost.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code loopPost.code ∧ localsResultRel ctxt live result sourceFinal loopPost := by
  let rows := programs.map (fun row => (row.2.1,row.2.2))
  let crep := compileProgExactHOLW panCtxt p
  let loop := compileHOLExact ctxt live crep
  let budget := callClockFactor ref rows source.clock crep * (sourceLimit+1)
  let factor := max (callSyntaxCost ref crep) (loopCodeWeight target.code+2)
  let start := {target with clock := target.clock+budget}
  obtain ⟨loopPost,ev,visitBound,st,mem,gl,code,locals⟩ :=
    callFrontend_wholeVisits_explicit panCtxt p shape programs sources ref ctxt live source sourceFinal result target
      sourceCode run nonerror nonTimeout sourceLimit sourceBound stateRel memRel globalsRel codeRel targetTable localsRel
  have mappedNonerror : resultToLoop result ≠ some .error := by
    cases result with
    | none => simp [resultToLoop]
    | some r => cases r <;> simp_all [resultToLoop]
  have simulation := loopTable_correct_with_steps (C := C) loop start
    (callFrontend_compiled_loopShape shape ctxt live) (by simpa [start] using targetTable)
  obtain ⟨wordPost,wordResult,wordRun,ffi,resCase,wordBound⟩ := simulation (resultToLoop result) loopPost word wordCtxt retv label
    ⟨ev,mappedNonerror,wordRel,by simpa [start] using wordLocals,retvLookup,dim,notWord,acc⟩
  have bound := wordBound.trans (Nat.mul_le_mul_left 6 visitBound)
  have mappedNoTimeout : resultToLoop result ≠ some .timeOut := by
    cases result with
    | none => simp [resultToLoop]
    | some r => cases r <;> simp_all [resultToLoop]
  have wordNoTimeout := resultCase_noTimeout wordCtxt retv word (resultToLoop result) loopPost wordResult wordPost resCase mappedNoTimeout
  have wordNoMt : WordProps.noMtCode word.code := by rw [wordCode]; exact LoopToWord.loop_compile_no_mt_code wordTable
  have wordNoInstall : WordProps.noInstallCode word.code := by rw [wordCode]; exact LoopToWord.loop_compile_no_install_code wordTable
  have normalized := WordToStackSteps.tableWord_normalized_run _ word wordPost wordResult _
    (loopComp_noMt loop wordCtxt label) (loopComp_noInstall loop wordCtxt label)
    wordNoMt wordNoInstall wordRun wordNoTimeout bound
  exact ⟨loopPost,wordPost,wordResult,ev,visitBound,wordRun,ffi,resCase,bound,normalized,st,mem,gl,code,locals⟩

/-- Compose the declaration-based source bound with the existing call-aware
Loop and Word simulations, using an explicit source control-step limit. -/
theorem callFrontend_declaration_word_explicit {C σ : Type}
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
    (word : WordSemStateFiniteExact 64 C σ) (wordCtxt : Spt Nat) (retv : WordLocW 64) (label : Nat × Nat)
    (wordCode : word.code = sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW declarations))))
    (wordRel : let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0 (getEidsFromDeclsHOL declarations)
      let programs := compileProgDeclsHOLW declarations
      let crep := compileProgExactHOLW panCtxt program
      let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * sourceLimit
      let rows := programs.map (fun row => (row.2.1,row.2.2))
      let budget := callClockFactor ref rows source.clock crep * (limit+1)
      loopToWordStateRelHOLExact {loop with clock := loop.clock+budget} word)
    (wordLocals : LoopToWord.localsRelHOL wordCtxt loop.locals word.locals)
    (retvLookup : sptLookup 0 word.locals = some retv) (notWord : ¬ wordSemIsWordLoc retv = true)
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
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let loopProgram := compileHOLExact ctxt live crep
    let factor := max (callSyntaxCost ref crep) (loopCodeWeight loop.code+2)
    let bound := 6 * (callSyntaxCost ref crep + factor * (source.clock+budget))
    ∃ crepFinal loopFinal wordFinal,
      evalCrepSemHOLProgExact (concreteDeclCrepState source programs) crep = (some (.return [.word value]),crepFinal) ∧
      evaluate loopProgram {loop with clock := loop.clock+budget} = (some (.result [.word value]),loopFinal) ∧
      LoopSteps.steps loopProgram {loop with clock := loop.clock+budget} ≤
        callSyntaxCost ref crep + factor * (source.clock+budget) ∧
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL wordCtxt loopProgram label).1
        {word with clock := bound} = (some (.result retv [.word value]),wordFinal) ∧
      WordSteps.steps (LoopToWord.compHOL wordCtxt loopProgram label).1 word ≤ bound ∧
      wordFinal.ffi = sourceFinal.ffi := by
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
    (getEidsFromDeclsHOL declarations)
  let programs := compileProgDeclsHOLW declarations
  let crep := compileProgExactHOLW panCtxt program
  let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * sourceLimit
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  obtain ⟨crepResult,crepFinal,crepRun,panRel,_,_,resultRel,crepBound⟩ :=
    callFrontend_declaration_steps declarations unique noInline shapes program shape source sourceFinal
      (some (.returned (.val (.word value)))) code locals globals structs exceptions noExceptions run (by simp)
      sourceLimit sourceBound
  have resultEq : crepResult = some (.return [.word value]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  rw [resultEq] at crepRun
  have sources : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q := by
    dsimp [programs]
    rw [compileProgDeclsHOLW,noInline,CrepInlineRoute.compileInlTopHOLExact_nil]
    exact callFrontend_declaration_sources declarations shapes
  have codeRel : crepToLoopCodeRelExact ctxt (concreteDeclCrepState source programs).code loop.code := by
    rw [loopCode]
    exact callFrontend_declaration_crepLoop_codeRel arch declarations noInline shapes start entry unique found
  have table : LoopTableSupported loop.code := by
    rw [loopCode]
    exact callFrontend_declaration_loopTableSupported arch declarations noInline shapes
  have wordSpan := callFrontend_word_explicit panCtxt program shape programs sources ref ctxt live
    (concreteDeclCrepState source programs) crepFinal (some (.return [.word value])) loop rfl crepRun (by simp) (by simp)
    limit crepBound stateRel memRel globalsRel codeRel table localsRel word wordCtxt retv label _ wordCode
    (by simpa [panCtxt,programs,crep,limit,concreteDeclCrepState] using wordRel)
    wordLocals retvLookup (Or.inr rfl) notWord acc
  obtain ⟨loopFinal,wordPost,wordResult,loopRun,loopBound,_,wordFfi,resultCase,wordBound,normalized,loopState,_,_,_,_⟩ := wordSpan
  have wordResultEq : wordResult = some (.result retv [.word value]) := by
    simpa [LoopToWord.CompileCorrect.resultCase,resultToLoop,wlabWlocExact] using resultCase.2.1
  rw [wordResultEq] at normalized
  rcases panRel with ⟨_,_,_,_,_,_,_,panFfi,_,_⟩
  refine ⟨crepFinal,loopFinal,_,crepRun,?_,?_,normalized,wordBound,?_⟩
  · simpa [panCtxt,programs,crep,limit,ctxt,concreteDeclCrepState,resultToLoop,wlabWlocExact] using loopRun
  · simpa [panCtxt,programs,crep,limit,ctxt,concreteDeclCrepState] using loopBound
  · exact wordFfi.trans (loopState.2.2.2.2.1.symm.trans panFfi.symm)

end FrontendBound

/-- A reached entry in a supported table has the complete sixfold compiler
simulation, including calls to other entries. -/
theorem loopTable_entry_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (List Nat × HolLoopProg width)) (loc : Nat) (params : List Nat) (body : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) (codeEq : s.code = code)
    (supported : LoopTableSupported code) (found : sptLookup loc code = some (params,body)) :
    SixBoundPropertyAt C body s := by
  apply loopTable_correct_with_steps body s (supported loc params body found)
  simpa only [codeEq] using supported

/-- The actual compiler table built from call-aware declarations discharges the
Loop-to-Word table premise when the declarations select no inlining. -/
theorem declaration_loopTable_entry_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (declarations : List (Pancake.PanLang.DeclHOL width))
    (noInline : (Pancake.PanLang.functionsHOL (declarations.filter Pancake.PanLang.inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ Pancake.PanLang.functionsHOL declarations,
      PanToCrepSteps.CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (Pancake.PanLang.functionsHOL declarations))
        (Pancake.PanLang.sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1)
    (loc : Nat) (params : List Nat) (body : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (codeEq : s.code = sptFromAList (compileProgHOLExact arch (compileProgDeclsHOLW declarations)))
    (found : sptLookup loc s.code = some (params,body)) : SixBoundPropertyAt C body s := by
  have table : LoopTableSupported s.code := by
    rw [codeEq]
    exact CrepToLoopSteps.callFrontend_declaration_loopTableSupported arch declarations noInline shapes
  exact loopTable_correct_with_steps body s (table loc params body found) table

end SteppedFlapjack.LoopToWordSteps
