import SteppedFlapjack.LoopToWordSteps.GlobalFrontendSpan
import SteppedFlapjack.Concrete.NestedMachine
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps

/-- Code-derived optimizer visit limit for the global-aware entry. -/
def globalProgramOptLimit (globals : PanGlobalsContextExact 64) (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (crep : CrepSemHOLState 64 Unit) (programs : List (MlS × List Nat × CrepProgHOL 64))
    (sourceLimit : Nat) (ref ctxt : CrepToLoopContextExact) (live : NumSet) : Nat :=
  let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
  let loopCode := sptFromAList (compileProgHOLExact riscvConfig.isa programs)
  let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
  let extra := callClockFactor ref (programs.map (fun row => (row.2.1,row.2.2))) crep.clock body * (crepLimit+1)
  let factor := max (callSyntaxCost ref body) (loopCodeWeight loopCode+2)
  let loopLimit := callSyntaxCost ref body + factor * (crep.clock+extra)
  let optimized := optimiseHOL (compileHOLExact ctxt live body)
  loopVisitWeight optimized + max (loopVisitWeight optimized) (loopCodeWeight loopCode+2) * (2*loopLimit)

/-- A global-aware source return reaches the native initialized Word state. -/
theorem globalConfiguredWord
    (globals : PanGlobalsContextExact 64) (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : GlobalCallFrontend globals panCtxt p)
    (source sourceFinal panTarget : PanSemStateFiniteExact 64 Unit) (value : BitVec 64)
    (crep : CrepSemHOLState 64 Unit) (programs : List (MlS × List Nat × CrepProgHOL 64)) (sourceLimit : Nat)
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
    (ref ctxt : CrepToLoopContextExact) (ctxtVars : ctxt.vars = HolFiniteMapExact.empty)
    (crepGlobals : crep.globals = HolFiniteMapExact.empty) (crepLocals : crep.locals = HolFiniteMapExact.empty)
    (codeRel : crepToLoopCodeRelExact ctxt crep.code (sptFromAList (compileProgHOLExact riscvConfig.isa programs)))
    (heap : crep.topAddr = crep.baseAddr + 2 * fixtureHeapLength)
    (memDomain : crep.memaddrs = ordinaryAddress) (sharedDomain : crep.shMemaddrs = sharedAddress)
    (base : crep.baseAddr = heapBase) (byteOrder : crep.be = false) (ffi : crep.ffi = sourceFfi)
    (cfg : LabToTarget.Config)
    (entry : let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
      (64,[],optimiseHOL (compileHOLExact ctxt .ln body)) ∈ compileProgHOLExact riscvConfig.isa programs)
    (fits : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
      let words := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      0xa0020018 + (compileNative riscvConfig false words).1.length*8 ≤ sourceBase)
    (good : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
      let words := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      StackToLab.Proofs.GoodCode.goodCode 24 (compileNative riscvConfig false words).2.2.2)
    (sourceMemory : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
      let words := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let bs := (compileNative riscvConfig false words).1
      ∀ address, crep.memaddrs address → crep.memory address = (sourceTemplateFor bs.length).memory address) :
    let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
    let words := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
    let native := compileNative riscvConfig false words
    let code := native.2.2.2
    let bs := native.1
    let limit := globalProgramOptLimit globals panCtxt p crep programs sourceLimit ref ctxt .ln
    ∃ final,
      WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
        {(configuredWord code words cfg bs) with clock := 6*limit+1} =
          (some (.result (.loc 1 0) [.word value]),final) ∧ sourceFinal.ffi = final.ffi := by
  let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let words := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
  let native := compileNative riscvConfig false words
  let code := native.2.2.2
  let bs := native.1
  let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
  let optimized := optimiseHOL (compileHOLExact ctxt .ln body)
  let wordCtxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL (sptDifference (accVarsHOL optimized .ln) (LoopToWord.toNumSetHOL []))) .ln
  let entryWord := ((sptLookup 64 (sptFromAList words)).getD (1,.skip)).2
  let frame := (compileProgNative riscvConfig false entryWord 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let template := configuredWord code words cfg bs
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have member : (64,1,(LoopToWord.compHOL wordCtxt optimized (64,2)).1) ∈ raw := by
    apply List.mem_map.mpr
    exact ⟨(64,[],optimized),entry,by simp [loopToWordCompFuncHOL,wordCtxt]⟩
  have unique : (raw.map Prod.fst).Nodup := by
    simpa [raw,loopToWordCompileHOL,loopToWordCompileProgHOL,List.map_map,Function.comp_def] using
      firstCompileProgAllDistinctExact riscvConfig.isa programs
  have out := (wholeCompile_entry_lookups phase3WordConfig riscvConfig raw 64 1 _ member unique).2
  have lookup : sptLookup 64 (sptFromAList words) = some (1,entryWord) := by
    dsimp only [entryWord]
    rw [show sptLookup 64 (sptFromAList words) = _ from (by simpa [words,compileWith_eq_compile _ allocator] using out)]
    rfl
  have frameLookup : sptLookup 64 template.stackSize = some frame := by
    simp [template,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,sptLookupMapi,lookup,frame]
  have memRel : crepToLoopMemRelHOLExact crep.memory (configuredStack code cfg bs).memory crep.memaddrs := by
    intro address member
    rw [sourceMemory address member]
    exact configuredStack_sourceMemory code cfg bs fits good address (by simpa [memDomain,sourceTemplateFor,sourceTemplate] using member)
  have result := globalCallFrontend_word_with_steps globals panCtxt p shape source sourceFinal panTarget value crep programs sourceLimit
    sourceTable compiledTable targetTable run sourceBound globalRel panCrepRel panCodeRel excpRel panLocalsRel sources
    riscvConfig.isa ref ctxt .ln rfl ctxtVars crepGlobals crepLocals (configuredStack code cfg bs).memory memRel codeRel
    fixtureHeapLength heap template 64 frame phase3WordConfig riscvConfig entry
  obtain ⟨post,wordRun,wordBound,wordFfi⟩ := result
  let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
  let crepLimit := max (SteppedFlapjack.CrepSteps.statementWeight body) (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit
  let extra := callClockFactor ref (programs.map (fun row => (row.2.1,row.2.2))) crep.clock body * (crepLimit+1)
  let clocked := {crep with clock := crep.clock+extra}
  let limit := globalProgramOptLimit globals panCtxt p crep programs sourceLimit ref ctxt .ln
  have codeEq : template.code = sptFromAList (compile phase3WordConfig riscvConfig raw).2 := by
    simp [template,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,words,compileWith_eq_compile _ allocator]
  have starter := configuredStarter_general clocked memDomain sharedDomain base byteOrder ffi programs code words cfg bs fits good
    frame (6*limit+1) frameLookup
  have eq : {(phase3Starter riscvConfig.isa clocked programs template fixtureHeapLength 64 frame) with
      memory := (configuredStack code cfg bs).memory, clock := 6*limit+1, code := sptFromAList (compile phase3WordConfig riscvConfig raw).2} =
      {template with clock := 6*limit+1} := by
    rw [← codeEq]
    simpa [template] using starter
  change WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
    {(phase3Starter riscvConfig.isa clocked programs template fixtureHeapLength 64 frame) with
      memory := (configuredStack code cfg bs).memory, clock := 6*limit+1, code := sptFromAList (compile phase3WordConfig riscvConfig raw).2} = _ at wordRun
  rw [eq] at wordRun
  exact ⟨post,wordRun,wordFfi⟩
end SteppedFlapjack.Concrete
