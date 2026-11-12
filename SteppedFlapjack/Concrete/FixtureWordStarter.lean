import SteppedFlapjack.Concrete.CountedSpan
import SteppedFlapjack.Concrete.FixtureCrepMemory
import SteppedFlapjack.Concrete.WordStarter
import Flapjack.Misc.Sptree.InsertUnchanged
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
namespace SteppedFlapjack.Concrete

/-- Word initialization over a concrete initialized Stack state and code table. -/
noncomputable def configuredWord (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :=
  makeInit riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (configuredStack code cfg bs) (sptFromAList words) (configuredWordOracle cfg bs)

/-- The initialized Stack state uses the backend garbage collector. -/
theorem configuredGc (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :
  (configuredStack code cfg bs).gcFun = WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf := by
  unfold configuredStack
  rw [fullMakeInit_eq]
  rfl

/-- A Crep state with fixture domains and metadata produces the native initialized Word starter. -/
theorem configuredStarter_general (source : CrepSemHOLState 64 Unit)
    (memDomain : source.memaddrs = ordinaryAddress) (sharedDomain : source.shMemaddrs = sharedAddress)
    (base : source.baseAddr = heapBase) (byteOrder : source.be = false) (ffi : source.ffi = sourceFfi)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (cfg : LabToTarget.Config) (bs : List (BitVec 64))
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (frame clock : Nat)
    (frameLookup : sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame) :
    {(phase3Starter riscvConfig.isa source crepPrograms (configuredWord code words cfg bs) fixtureHeapLength 64 frame) with
      memory := (configuredStack code cfg bs).memory, clock := clock, code := (configuredWord code words cfg bs).code} =
    {(configuredWord code words cfg bs) with clock := clock} := by
  classical
  have ambient := configuredStack_ambient code cfg bs fits good
  have current := (configuredStack_heapBaseAndMemory code cfg bs fits good).1
  have len := configuredStack_heapLength code cfg bs fits good
  have fr := sptInsertUnchanged (configuredWord code words cfg bs).stackSize 64 frame frameLookup
  simp only [configuredWord,makeInit] at fr
  have existing {α β : Type} [DecidableEq α] (m : HolFiniteMapExact α β) (k : α) (v : β) (h : m.lookup k = some v) : m.updateEq (k,v) = m := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]
    split
    · rename_i eq
      subst key
      exact h.symm
    · rfl
  have cur : ((configuredStack code cfg bs).store.eraseEq .handler).lookup .currHeap = some (.word heapBase) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using current
  have length : ((configuredStack code cfg bs).store.eraseEq .handler).lookup .heapLength = some (.word fixtureHeapLength) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using len
  have domain : (concreteDeclLoopState riscvConfig.isa source crepPrograms).mdomain = (configuredStack code cfg bs).mdomain := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simpa [concreteDeclLoopState,memDomain] using (configuredStack_heapDomain code cfg bs fits good a).symm
  have shared : (concreteDeclLoopState riscvConfig.isa source crepPrograms).shMdomain = (configuredStack code cfg bs).shMdomain := by
    simp [concreteDeclLoopState,sharedDomain,ambient.2.2]
  simp only [phase3Starter,concreteDeclWordState]
  rw [domain,shared]
  simp [base,byteOrder,ffi,configuredWord,makeInit,configuredGc]
  refine ⟨by rw [existing _ _ _ cur,existing _ _ _ length],fr,?_,?_⟩
  · exact ambient.2.1
  · exact ambient.1.symm

/-- The generated optimized entry and its native frame are present in initialized Word state. -/
theorem functionOnly_initializedEntry (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :
    let programs := compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)
    let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
    let optimized := (compile wc riscvConfig raw).2
    let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
    let frame := (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
    sptLookup 64 (configuredWord code optimized cfg bs).code = some (1,entry) ∧
      sptLookup 64 (configuredWord code optimized cfg bs).stackSize = some frame := by
  let decls := compileTopExactHOL (fs.map DeclHOL.function) start
  let programs := compileProgDeclsHOLW decls
  let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
  let crep := compileProgExactHOLW pan p
  let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let loop := optimiseHOL (compileHOLExact ctxt .ln crep)
  let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let optimized := (compile wc riscvConfig raw).2
  let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
  let frame := (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  have member : (64,1,loopToWordCompFuncHOL 64 [] loop) ∈ raw := by
    simpa [raw,loop,ctxt,crep,p,pan,programs,decls,firstLoopName] using functionOnly_wordEntry fs start body found noInline riscvConfig.isa
  have nodup : (raw.map Prod.fst).Nodup := by
    simpa [raw,loopToWordCompileHOL,loopToWordCompileProgHOL,List.map_map,Function.comp_def] using
      firstCompileProgAllDistinctExact riscvConfig.isa programs
  have out := (wholeCompile_entry_lookups wc riscvConfig raw 64 1 _ member nodup).2
  have lookup : sptLookup 64 (sptFromAList optimized) = some (1,entry) := by
    dsimp only [entry]
    rw [show sptLookup 64 (sptFromAList optimized) = _ from out]
    rfl
  constructor
  · simpa [configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit] using lookup
  · change sptLookup 64 (configuredWord code optimized cfg bs).stackSize = some frame
    simp [configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,sptLookupMapi,lookup,frame]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- A counted source return reaches the native initialized Word start at an explicit bound. -/
theorem countedCalls_initializedWord {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program)     (production : PanSemState (RiscV.Word 64) (FfiState Unit)) (source : PanSemStateFiniteExact 64 Unit)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words_ : WordLocals production.locals)
    (byteRanged : ProgByteRanged program)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body)
    (targetCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (codeRel : PanSimp.CodeRel source.code targetCode)
    (entries : List SimpVisits.SimpEntry)
    (sourceCode : source.code = HolFiniteMapExact.empty.updateList entries.reverse)
    (entryShapes : ∀ entry ∈ entries, ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program)
    (fs : List (FunDeclHOL 64)) (start : MlS)
    (targetTable : targetCode = HolFiniteMapExact.empty.updateList (functionsHOL (fs.map DeclHOL.function)).reverse)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],progToHOL (panSimpProg program),.one))
    (mainFound : source.code.lookup start = some ([],progToHOL program,.one))
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (unique : ((functionsHOL (fs.map DeclHOL.function)).map Prod.fst).Nodup)
    (shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ body : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (Flapjack.Basis.Pure.MlString.ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL body ∧ CallSupportedIn names body ∧ ProgByteRanged body)
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (exnContracts : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ source.clock) (wc : Flapjack.Compiler.Backend.WordToWord.Config) (nativeCode : List (Nat × StackLang.HolProg 64))
    (cfg : LabToTarget.Config) (bitmaps : List (BitVec 64))
    (fits : 0xa0020018 + bitmaps.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 nativeCode)
    (memDomain : source.memaddrs = ordinaryAddress) (sharedDomain : source.shMemaddrs = sharedAddress)
    (base : source.baseAddr = heapBase) (top : source.topAddr = heapTop)
    (byteOrder : source.be = false) (ffi : source.ffi = sourceFfi)
    (sourceMemory : ∀ a, source.memaddrs a → source.memory a = (sourceTemplateFor bitmaps.length).memory a)
:
    let decls := fs.map DeclHOL.function
    let lowered := compileTopExactHOL decls start
    let renamed := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
    let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
    let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
    let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
    let programs := compileProgDeclsHOLW lowered
    let crep := compileProgExactHOLW pan p
    let initial := concreteDeclCrepState before programs
    let loop := {(concreteDeclLoopState riscvConfig.isa initial programs) with memory := (configuredStack nativeCode cfg bitmaps).memory}
    let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let crepLimit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) *
      (1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2)
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let extra := callClockFactor ctxt rows initial.clock crep * (crepLimit+1)
    let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
    let loopLimit := callSyntaxCost ctxt crep + factor * (initial.clock+extra)
    let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
    let optFactor := max (loopVisitWeight opt) (loopCodeWeight loop.code+2)
    let optLimit := loopVisitWeight opt + optFactor * (2 * loopLimit)
    let words := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
    let optimized := (compile wc riscvConfig words).2
    let word := {(configuredWord nativeCode optimized cfg bitmaps) with clock := 6*optLimit+1}
    ∃ (sourceFinal : PanSemStateFiniteExact 64 Unit) (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Unit),
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none) word =
        (some (.result (.loc 1 0) [.word value]),post) ∧
      WordSteps.steps (.call none (some firstLoopName) [0] none) word ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc riscvConfig words).2)) * (6*optLimit+1) ∧
      post.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  let decls := fs.map DeclHOL.function
  let lowered := compileTopExactHOL decls start
  let programs := compileProgDeclsHOLW lowered
  let renamed : PanSemStateFiniteExact 64 Unit := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
  let initial := concreteDeclCrepState before programs
  let loop := {(concreteDeclLoopState riscvConfig.isa initial programs) with memory := (configuredStack nativeCode cfg bitmaps).memory}
  let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let crep := compileProgExactHOLW pan p
  let crepLimit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) *
    (1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2)
  let rows := programs.map (fun row => (row.2.1,row.2.2))
  let extra := callClockFactor ctxt rows initial.clock crep * (crepLimit+1)
  let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
  let loopLimit := callSyntaxCost ctxt crep + factor * (initial.clock+extra)
  let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
  let optFactor := max (loopVisitWeight opt) (loopCodeWeight loop.code+2)
  let optLimit := loopVisitWeight opt + optFactor * (2*loopLimit)
  let replay := {initial with clock := loop.clock+extra}
  let words := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let optimized := (compile wc riscvConfig words).2
  let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
  let frame := (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false entry 1
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let template := configuredWord nativeCode optimized cfg bitmaps
  have frameLookup : sptLookup 64 template.stackSize = some frame :=
    (functionOnly_initializedEntry fs start (progToHOL (panSimpProg program)) found noInline
      wc nativeCode cfg bitmaps).2
  have memoryRel : crepToLoopMemRelHOLExact source.memory (configuredStack nativeCode cfg bitmaps).memory source.memaddrs := by
    intro a ha
    rw [sourceMemory a ha]
    exact configuredStack_sourceMemory nativeCode cfg bitmaps fits good a (by simpa [memDomain,sourceTemplateFor,sourceTemplate] using ha)
  have heap : source.topAddr = source.baseAddr + 2 * fixtureHeapLength := by
    rw [top,base]
    decide
  obtain ⟨sourceFinal,post,sourceRun,wordRun,wordBound,wordFfi,ffiRel⟩ :=
    countedCalls_functionOnlyWord supported production source rel ranged words_ byteRanged codeRanged codeShape
      targetCode codeRel entries sourceCode entryShapes fs start targetTable found mainFound locals globals structs
      exceptions unique shapes noInline topOutside aligned context primitive handler exnContracts fuel count
      postLocals postGlobals postMemory postFfi value run budget riscvConfig.isa
      (configuredStack nativeCode cfg bitmaps).memory memoryRel template fixtureHeapLength frame wc riscvConfig heap
  have codeEq : template.code = sptFromAList optimized := by
    simp [template,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit]
  have starter := configuredStarter_general replay
    (by simpa [replay,initial,concreteDeclCrepState,before,noGlobalsLoweredPreCall,renamed] using memDomain)
    (by simpa [replay,initial,concreteDeclCrepState,before,noGlobalsLoweredPreCall,renamed] using sharedDomain)
    (by simpa [replay,initial,concreteDeclCrepState,before,noGlobalsLoweredPreCall,renamed] using base)
    (by simpa [replay,initial,concreteDeclCrepState,before,noGlobalsLoweredPreCall,renamed] using byteOrder)
    (by simpa [replay,initial,concreteDeclCrepState,before,noGlobalsLoweredPreCall,renamed] using ffi)
    programs nativeCode optimized cfg bitmaps fits good frame (6*optLimit+1) frameLookup
  have eq : {(phase3Starter riscvConfig.isa replay programs template fixtureHeapLength firstLoopName frame) with
      memory := (configuredStack nativeCode cfg bitmaps).memory, clock := 6*optLimit+1, code := sptFromAList optimized} =
      {template with clock := 6*optLimit+1} := by
    rw [← codeEq]
    simpa [firstLoopName] using starter
  change WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none)
    {(phase3Starter riscvConfig.isa replay programs template fixtureHeapLength firstLoopName frame) with
      memory := (configuredStack nativeCode cfg bitmaps).memory, clock := 6*optLimit+1, code := sptFromAList optimized} = _ at wordRun
  change WordSteps.steps (.call none (some firstLoopName) [0] none)
    {(phase3Starter riscvConfig.isa replay programs template fixtureHeapLength firstLoopName frame) with
      memory := (configuredStack nativeCode cfg bitmaps).memory, clock := 6*optLimit+1, code := sptFromAList optimized} ≤ _ at wordBound
  rw [eq] at wordRun wordBound
  exact ⟨sourceFinal,post,sourceRun,wordRun,wordBound,wordFfi,ffiRel⟩

end SteppedFlapjack.Concrete
