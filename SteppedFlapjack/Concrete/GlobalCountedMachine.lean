import SteppedFlapjack.Concrete.GlobalSourceMachine
import SteppedFlapjack.Concrete.GlobalFrontendShape
import SteppedFlapjack.Concrete.GlobalDecodedLayout
import SteppedFlapjack.PanToCrepSteps.GlobalInitializedEntry
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem bitmapFits_sourceBase (n : Nat) (h : 0xa0020018 + n*8 ≤ 0xa0410000) :
    0xa0020018 + n*8 ≤ sourceBase := by
  simp only [sourceBase]
  omega

/-- A lowered Pancake run reaches its initialized RISC-V compilation. -/
private theorem loweredSource_machine
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : CallFrontend panCtxt p)
    (source sourceFinal : PanSemStateFiniteExact 64 Unit) (value : BitVec 64)
    (crep : CrepSemHOLState 64 Unit) (sourceLimit : Nat)
    (compiledTable : crep.code = alistToFmapCodeExact (globalSourcePrograms pan))
    (targetTable : CallFrontendCode panCtxt source.code)
    (run : source.evaluateHOLFiniteState p = (some (.returned (.val (.word value))),sourceFinal))
    (sourceBound : controlSteps p source ≤ sourceLimit)
    (panCrepRel : panToCrepStateRelFiniteExact source crep)
    (panCodeRel : codeRelExactHOLW panCtxt source.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact panCtxt.eids source.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact panCtxt source.locals crep.locals)
    (sources : ∀ row ∈ globalSourcePrograms pan, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (ref ctxt : CrepToLoopContextExact) (ctxtVars : ctxt.vars = HolFiniteMapExact.empty)
    (crepGlobals : crep.globals = HolFiniteMapExact.empty) (crepLocals : crep.locals = HolFiniteMapExact.empty)
    (codeRel : crepToLoopCodeRelExact ctxt crep.code (sptFromAList (compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))))
    (heap : crep.topAddr = crep.baseAddr + 2 * fixtureHeapLength)
    (memDomain : crep.memaddrs = ordinaryAddress) (sharedDomain : crep.shMemaddrs = sharedAddress)
    (base : crep.baseAddr = heapBase) (byteOrder : crep.be = false) (ffi : crep.ffi = sourceFfi)
    (entry : let body := compileProgExactHOLW panCtxt (p)
      (64,[],optimiseHOL (compileHOLExact ctxt .ln body)) ∈ compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))
    (bitmapFits : 0xa0020018 + (globalSourceBitmaps pan).length*8 ≤ 0xa0410000)
    (safe : fixtureStackSafe (globalSourceCode pan) = true)
    (facts : (fixtureRemoveLabels (globalSourceCode pan)).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode pan)).length ≤ 0xecc ∧ (fixtureCodeBytes (globalSourceCode pan)).length % 4 = 0)
    (capacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame pan)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames pan) 64 (sptFromAList (globalSourceWords pan))))) (some 2097172))
    (sourceMemory : ∀ address, crep.memaddrs address → crep.memory address = (sourceTemplateFor (globalSourceBitmaps pan).length).memory address) :
    let code := globalSourceCode pan
    let bs := globalSourceBitmaps pan
    let words := globalSourceWords pan
    let limit := loweredProgramOptLimit panCtxt p crep (globalSourcePrograms pan) sourceLimit ref ctxt .ln
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let programs := globalSourcePrograms pan
  let raw := globalSourceRaw pan
  let words := globalSourceWords pan
  let code := globalSourceCode pan
  let bs := globalSourceBitmaps pan
  let cfg := fixtureCompilerConfig code
  let limit := loweredProgramOptLimit panCtxt p crep programs sourceLimit ref ctxt .ln
  have rawEq : panToWordCompileProgHOL riscvConfig.isa pan = raw := by rfl
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have good : StackToLab.Proofs.GoodCode.goodCode 24 code := by
    have h := source_nativeGoodCode pan unique
    rw [rawEq, ← phase3WordConfig_eq] at h
    simpa [code,globalSourceCode,globalSourceNative,words,globalSourceWords,compileWith_eq_compile _ allocator] using h
  have fits : 0xa0020018 + bs.length*8 ≤ sourceBase := bitmapFits_sourceBase bs.length bitmapFits
  obtain ⟨wordPost,wordRun,wordFfi⟩ := loweredConfiguredWord panCtxt p shape source sourceFinal value
    crep programs sourceLimit compiledTable targetTable run sourceBound panCrepRel panCodeRel
    excpRel panLocalsRel sources ref ctxt ctxtVars crepGlobals crepLocals codeRel heap memDomain sharedDomain base byteOrder ffi
    cfg entry fits good sourceMemory
  let body := compileProgExactHOLW panCtxt (p)
  let optimized := optimiseHOL (compileHOLExact ctxt .ln body)
  let wordCtxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL (sptDifference (accVarsHOL optimized .ln) (LoopToWord.toNumSetHOL []))) .ln
  have member : (64,1,(LoopToWord.compHOL wordCtxt optimized (64,2)).1) ∈ raw := by
    apply List.mem_map.mpr
    exact ⟨(64,[],optimized),entry,by simp [loopToWordCompFuncHOL,wordCtxt]⟩
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := generated_initialized_machine programs _ member pan unique rawEq limit value
    sourceGood bitmapFits safe facts capacity wordPost wordRun
  exact ⟨finalMachine,finalFfi,machineRun,events.trans (congrArg (fun f => f.ioEvents) wordFfi.symm)⟩

def globalEntryTemplate (pan : List (DeclHOL 64)) (clock : Nat) : PanSemStateFiniteExact 64 Unit :=
  {(sourceTemplateFor (globalSourceBitmaps pan).length) with clock := clock+1}

def globalEntryTarget (pan : List (DeclHOL 64)) (clock : Nat) (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : PanSemStateFiniteExact 64 Unit :=
  installTargetFunctions (globalEntryTemplate pan clock) globals entries

def globalEntryCrep (pan : List (DeclHOL 64)) (clock : Nat) (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : CrepSemHOLState 64 Unit :=
  concreteDeclCrepState (globalEntryTarget pan clock globals entries) (globalSourcePrograms pan)

/-- Run the generated initializer and source call through the initialized machine. -/
private theorem initializedGlobal_machine
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (clock : Nat) (decs : List (DeclHOL 64)) (post : PanSemStateFiniteExact 64 Unit)
    (initializers : List (ProgHOL 64)) (funs exns : List (DeclHOL 64)) (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (name : MlS)
    (p : ProgHOL 64) (panCtxt : PanToCrepContextExact 64) (shape : GlobalCallFrontend globals panCtxt p)
    (value : BitVec 64) (sourceFinal : PanSemStateFiniteExact 64 Unit) (limit : Nat)
    (onlyDecls : ∀ d ∈ decs, isDeclHOL d = true)
    (initializerShape : ∀ sh n e, DeclHOL.decl sh n e ∈ decs → FrontendValue panCtxt e)
    (eval : @evaluateDeclsHOLFinite 64 Unit _
      (beforeGlobals (globalEntryTarget pan clock globals entries)
        (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
        ((decShapesHOL decs).map sizeOfShapeHOL).sum) (fun _a => Classical.propDecidable _) decs = some post)
    (compiled : compileDecsExactHOL
      (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)) decs =
        (initializers,funs,exns,globals))
    (allocated : ∀ a, addresses ((globalEntryTemplate pan clock).topAddr - panBytesInWord 64 *
      BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      ((decShapesHOL decs).map sizeOfShapeHOL).sum a → (globalEntryTemplate pan clock).memaddrs a)
    (sizeBound : (panBytesInWord 64).toNat * ((decShapesHOL decs).map sizeOfShapeHOL).sum < 2 ^ 64)
    (found : entries.lookup name = some ([],p,.one))
    (sourceTable : GlobalCallTable globals (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).code)
    (run : (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).evaluateHOLFiniteState p =
      (some (.returned (.val (.word value))),sourceFinal))
    (bound : controlSteps p (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty) ≤ limit)
    (targetTable : CallFrontendCode panCtxt (globalEntryTarget pan clock globals entries).code)
    (panCodeRel : codeRelExactHOLW panCtxt (globalEntryTarget pan clock globals entries).code
      (globalEntryCrep pan clock globals entries).code)
    (varsEmpty : panCtxt.vars = HolFiniteMapExact.empty) (exceptionsEmpty : panCtxt.eids = HolFiniteMapExact.empty)
    (sources : ∀ row ∈ globalSourcePrograms pan, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (codeRel : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
      crepToLoopCodeRelExact ctxt (globalEntryCrep pan clock globals entries).code
        (sptFromAList (compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))))
    (entry : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
      let body := compileProgExactHOLW panCtxt (.seq (nestedSeqHOL initializers) (.call none name []))
      (64,[],optimiseHOL (compileHOLExact ctxt .ln body)) ∈ compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))
    (bitmapFits : 0xa0020018 + (globalSourceBitmaps pan).length*8 ≤ 0xa0410000)
    (safe : fixtureStackSafe (globalSourceCode pan) = true)
    (facts : (fixtureRemoveLabels (globalSourceCode pan)).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode pan)).length ≤ 0xecc ∧ (fixtureCodeBytes (globalSourceCode pan)).length % 4 = 0)
    (capacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame pan)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames pan) 64 (sptFromAList (globalSourceWords pan))))) (some 2097172)) :
    let code := globalSourceCode pan
    let bs := globalSourceBitmaps pan
    let words := globalSourceWords pan
    let crep := globalEntryCrep pan clock globals entries
    let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
    let body := .seq (nestedSeqHOL initializers) (.call none name [])
    let visitLimit := 2*decs.length+limit+3
    let opt := loweredProgramOptLimit panCtxt body crep (globalSourcePrograms pan) visitLimit ctxt ctxt .ln
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*opt+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*opt+1 + allowance)
    ∃ finalMachine finalFfi compilerFinal,
      Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig pan =
        some (fixtureCodeBytes code,bs,compilerFinal) ∧
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let template := globalEntryTemplate pan clock
  let target := globalEntryTarget pan clock globals entries
  let crep := globalEntryCrep pan clock globals entries
  let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
  have outside : ¬ template.memaddrs template.topAddr := by
    change ¬ ordinaryAddress heapTop
    decide
  have aligned : panGlobalsByteAlignedHOL template.topAddr := by
    change panGlobalsByteAlignedHOL heapTop
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  obtain ⟨targetFinal,targetRun,targetBound,targetFfi⟩ := globalInitializedEntry_return template decs post initializers funs exns globals
    entries name p panCtxt shape value sourceFinal limit rfl outside aligned (by simp [template,globalEntryTemplate])
    onlyDecls eval compiled allocated sizeBound found sourceTable run bound
  have initShape := globalCompile_frontend_initializer_sequence panCtxt decs initializerShape
    (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum))
  rw [compiled] at initShape
  have bodyShape : CallFrontend panCtxt (.seq (nestedSeqHOL initializers) (.call none name [])) :=
    .seq (.base initShape) (.tail (by simp))
  have stateRel : panToCrepStateRelFiniteExact target crep := by
    apply concreteDecl_panCrep_stateRel
    · rfl
    · rfl
  have localRel : panToCrepLocalsRelFiniteExact panCtxt target.locals crep.locals := by
    exact empty_panCrep_locals panCtxt _ varsEmpty
  have exRel : panToCrepExcpRelFiniteExact panCtxt.eids target.eshapes := by
    rw [exceptionsEmpty]
    exact empty_panCrep_exceptions
  have heap : crep.topAddr = crep.baseAddr + 2*fixtureHeapLength := by
    change heapTop = heapBase + 2*fixtureHeapLength
    decide
  have memory : ∀ address, crep.memaddrs address → crep.memory address = (sourceTemplateFor (globalSourceBitmaps pan).length).memory address := by
    intro address member
    rfl
  obtain ⟨machine,ffi,machineRun,events⟩ := loweredSource_machine pan unique sourceGood panCtxt _ bodyShape
    target (emptyLocalsHOLFinite targetFinal) value crep (2*decs.length+limit+3) rfl targetTable targetRun targetBound
    stateRel panCodeRel exRel localRel sources ctxt ctxt rfl rfl rfl codeRel heap rfl rfl rfl rfl rfl entry bitmapFits safe facts capacity memory
  obtain ⟨compilerFinal,compiledOutput⟩ := globalSource_compilerOutputFor pan pan rfl safe facts.1
  refine ⟨machine,ffi,compilerFinal,compiledOutput,machineRun,?_⟩
  simpa [emptyLocalsHOLFinite] using events.trans (congrArg (fun f => f.ioEvents) targetFfi.symm)

/-- A counted Supported source reaches the machine after real global initialization. -/
private theorem initializedGlobal_counted_machine_fromRel
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (clock : Nat) (decs : List (DeclHOL 64)) (post : PanSemStateFiniteExact 64 Unit)
    (initializers : List (ProgHOL 64)) (funs exns : List (DeclHOL 64)) (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (name : MlS)
    (program : Prog (RiscV.Word 64)) (shapes : VarName → Option ShapeHOL)
    (supported : Supported shapes program) (layout : GlobalLayout shapes globals)
    (panCtxt : PanToCrepContextExact 64) (production : PanSemState (RiscV.Word 64) (FfiState Unit)) (value : BitVec 64)
    (onlyDecls : ∀ d ∈ decs, isDeclHOL d = true)
    (initializerShape : ∀ sh n e, DeclHOL.decl sh n e ∈ decs → FrontendValue panCtxt e)
    (eval : @evaluateDeclsHOLFinite 64 Unit _
      (beforeGlobals (globalEntryTarget pan clock globals entries)
        (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
        ((decShapesHOL decs).map sizeOfShapeHOL).sum) (fun _a => Classical.propDecidable _) decs = some post)
    (compiled : compileDecsExactHOL
      (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)) decs =
        (initializers,funs,exns,globals))
    (allocated : ∀ a, addresses ((globalEntryTemplate pan clock).topAddr - panBytesInWord 64 *
      BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      ((decShapesHOL decs).map sizeOfShapeHOL).sum a → (globalEntryTemplate pan clock).memaddrs a)
    (sizeBound : (panBytesInWord 64).toNat * ((decShapesHOL decs).map sizeOfShapeHOL).sum < 2 ^ 64)
    (found : entries.lookup name = some ([],progToHOL program,.one))
    (productionRel : PanSemStateRelExec production
      (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).toExact)
    (productionRanged : PanSemStateRelExecRanged production) (wordsLocal : WordLocals production.locals)
    (globalShapes : GlobalHOLShapes shapes production.globals)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, GlobalCallSupportedIn shapes scope body)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (exceptions : InfoMap Shape)
    (fuel count : Nat) (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exceptions)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock)
    (targetTable : CallFrontendCode panCtxt (globalEntryTarget pan clock globals entries).code)
    (panCodeRel : codeRelExactHOLW panCtxt (globalEntryTarget pan clock globals entries).code
      (globalEntryCrep pan clock globals entries).code)
    (varsEmpty : panCtxt.vars = HolFiniteMapExact.empty) (exceptionsEmpty : panCtxt.eids = HolFiniteMapExact.empty)
    (sources : ∀ row ∈ globalSourcePrograms pan, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (codeRel : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
      crepToLoopCodeRelExact ctxt (globalEntryCrep pan clock globals entries).code
        (sptFromAList (compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))))
    (entry : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
      let body := compileProgExactHOLW panCtxt (.seq (nestedSeqHOL initializers) (.call none name []))
      (64,[],optimiseHOL (compileHOLExact ctxt .ln body)) ∈ compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))
    (bitmapFits : 0xa0020018 + (globalSourceBitmaps pan).length*8 ≤ 0xa0410000)
    (safe : fixtureStackSafe (globalSourceCode pan) = true)
    (facts : (fixtureRemoveLabels (globalSourceCode pan)).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode pan)).length ≤ 0xecc ∧ (fixtureCodeBytes (globalSourceCode pan)).length % 4 = 0)
    (capacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame pan)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames pan) 64 (sptFromAList (globalSourceWords pan))))) (some 2097172)) :
    let code := globalSourceCode pan
    let bs := globalSourceBitmaps pan
    let words := globalSourceWords pan
    let crep := globalEntryCrep pan clock globals entries
    let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
    let body := .seq (nestedSeqHOL initializers) (.call none name [])
    let visitLimit := 2*decs.length+(callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock+3
    let opt := loweredProgramOptLimit panCtxt body crep (globalSourcePrograms pan) visitLimit ctxt ctxt .ln
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*opt+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*opt+1 + allowance)
    ∃ sourceFinal : PanSemStateFiniteExact 64 Unit, ∃ finalMachine finalFfi compilerFinal,
      Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig pan =
        some (fixtureCodeBytes code,bs,compilerFinal) ∧
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel postFfi sourceFinal.ffi := by
  classical
  let source := callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty
  change count ≤ source.clock at budget
  have sourceTable := globalSupported_sourceTable shapes globals layout production source productionRel codeShape
  have shape : GlobalCallFrontend globals panCtxt (progToHOL program) :=
    globalCallSupported_frontend layout supported.1 panCtxt (by intro n member; simp at member)
  obtain ⟨holResult,sourceFinal,holRun,outcome,sourceBound,_,_⟩ :=
    globalSupportedCalls_counted_source supported.1 production source productionRel productionRanged wordsLocal globalShapes
      supported.2 codeRanged codeShape context primitive handler exceptions fuel count _ run budget
  cases outcome with
  | returned _ _ _ _ word final rel ranged words =>
    have bound : controlSteps (progToHOL program) source ≤ source.clock := by
      simp only [countedErrorBonus,Nat.add_zero] at sourceBound
      omega
    obtain ⟨machine,finalFfi,compilerFinal,compiledOutput,machineRun,events⟩ :=
      initializedGlobal_machine pan unique sourceGood clock decs post initializers funs exns globals entries name
        (progToHOL program) panCtxt shape value sourceFinal source.clock onlyDecls initializerShape eval compiled allocated
        sizeBound found sourceTable holRun bound targetTable panCodeRel varsEmpty exceptionsEmpty sources codeRel entry
        bitmapFits safe facts capacity
    exact ⟨sourceFinal,machine,finalFfi,compilerFinal,compiledOutput,machineRun,events,rel.2.2.2.2.2.2.2.2.2.2.1⟩

/-- A counted source reaches the machine from declaration-constructed source and target states. -/
theorem initializedGlobal_counted_machine
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (clock : Nat) (decs : List (DeclHOL 64)) (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (initializers : List (ProgHOL 64)) (funs exns : List (DeclHOL 64)) (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (name : MlS)
    (program : Prog (RiscV.Word 64)) (supported : Supported (globalEntryShapes post entries) program)
    (panCtxt : PanToCrepContextExact 64) (value : BitVec 64)
    (onlyDecls : ∀ d ∈ decs, isDeclHOL d = true)
    (initializerShape : ∀ sh n e, DeclHOL.decl sh n e ∈ decs → FrontendValue panCtxt e)
    (eval : @evaluateDeclsHOLFinite 64 Unit _
      (beforeGlobals (globalEntryTarget pan clock globals entries)
        (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
        ((decShapesHOL decs).map sizeOfShapeHOL).sum) (fun _a => Classical.propDecidable _) decs = some post)
    (compiled : compileDecsExactHOL
      (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)) decs =
        (initializers,funs,exns,globals))
    (allocated : ∀ a, addresses ((globalEntryTemplate pan clock).topAddr - panBytesInWord 64 *
      BitVec.ofNat 64 ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      ((decShapesHOL decs).map sizeOfShapeHOL).sum a → (globalEntryTemplate pan clock).memaddrs a)
    (sizeBound : (panBytesInWord 64).toNat * ((decShapesHOL decs).map sizeOfShapeHOL).sum < 2 ^ 64)
    (found : entries.lookup name = some ([],progToHOL program,.one))
    (supportedEntries : GlobalSupportedEntries (globalEntryShapes post entries) entries)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (exceptions : InfoMap Shape)
    (fuel count : Nat) (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit)
    (run : evalPanValueFfiProgSteps context primitive handler (globalEntryProduction post entries).structs (countedFunctionsOfCode (globalEntryProduction post entries).code)
      (globalEntryProduction post entries).baseAddress (globalEntryProduction post entries).topAddress panSemBitVec64BytesInWord fuel
      (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess (globalEntryProduction post entries)))
      (contracts := some (countedContractsOfCode (globalEntryProduction post entries).code exceptions)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock)
    (panCodeRel : codeRelExactHOLW panCtxt (globalEntryTarget pan clock globals entries).code
      (globalEntryCrep pan clock globals entries).code)
    (varsEmpty : panCtxt.vars = HolFiniteMapExact.empty) (exceptionsEmpty : panCtxt.eids = HolFiniteMapExact.empty)
    (sources : ∀ row ∈ globalSourcePrograms pan, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (rest : List (MlS × List Nat × CrepProgHOL 64))
    (programsUnique : ((globalSourcePrograms pan).map Prod.fst).Nodup)
    (first : globalSourcePrograms pan = (ofString "main",[],
      compileProgExactHOLW panCtxt (.seq (nestedSeqHOL initializers) (.call none name []))) :: rest)
    (bitmapFits : 0xa0020018 + (globalSourceBitmaps pan).length*8 ≤ 0xa0410000)
    (safe : fixtureStackSafe (globalSourceCode pan) = true)
    (facts : (fixtureRemoveLabels (globalSourceCode pan)).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode pan)).length ≤ 0xecc ∧ (fixtureCodeBytes (globalSourceCode pan)).length % 4 = 0)
    (capacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame pan)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames pan) 64 (sptFromAList (globalSourceWords pan))))) (some 2097172)) :
    let code := globalSourceCode pan
    let bs := globalSourceBitmaps pan
    let words := globalSourceWords pan
    let crep := globalEntryCrep pan clock globals entries
    let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
    let body := .seq (nestedSeqHOL initializers) (.call none name [])
    let visitLimit := 2*decs.length+(callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock+3
    let opt := loweredProgramOptLimit panCtxt body crep (globalSourcePrograms pan) visitLimit ctxt ctxt .ln
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*opt+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*opt+1 + allowance)
    ∃ sourceFinal : PanSemStateFiniteExact 64 Unit, ∃ finalMachine finalFfi compilerFinal,
      Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig pan =
        some (fixtureCodeBytes code,bs,compilerFinal) ∧
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel postFfi sourceFinal.ffi := by
  let target := globalEntryTarget pan clock globals entries
  have outside : ¬ target.memaddrs target.topAddr := by
    change ¬ ordinaryAddress heapTop
    decide
  have aligned : panGlobalsByteAlignedHOL target.topAddr := by
    change panGlobalsByteAlignedHOL heapTop
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  obtain ⟨final,_,rel,_,finalFfi,_,_⟩ := beforeGlobals_initializedFunctions target decs post initializers funs exns globals entries
    rfl outside aligned (by right; rfl) onlyDecls eval compiled allocated sizeBound
  have ffiEq : (globalEntrySource post entries).ffi = sourceFfi := by
    apply globalEntry_decodedFfi post final globals entries rel
    exact finalFfi
  have layout := globalEntry_decodedLayout post final globals entries rel
  have relExec := globalEntryProduction_related post entries ffiEq
  have ranged := globalEntryProduction_ranged post entries
  have localsWord := globalEntryProduction_localsWord post entries
  have globalShapes := globalEntryProduction_shapes post entries (globalEntryShapes post entries) (by intros; rfl)
  have codeRanged := globalEntryProduction_codeRanged post entries
  have sourceTableSupported := supported_source_table (globalEntryShapes post entries) entries supportedEntries
  have codeShape := globalEntryProduction_codeShape post entries (globalEntryShapes post entries) sourceTableSupported
  have targetTable := target_table_from_supported (globalEntryShapes post entries) globals layout
    (globalEntryTemplate pan clock) panCtxt entries supportedEntries
  let body := compileProgExactHOLW panCtxt (.seq (nestedSeqHOL initializers) (.call none name []))
  have bodyMember : (ofString "main",[],body) ∈ globalSourcePrograms pan := by rw [first]; simp [body]
  have bodyFixed : crepSimpProgHOL body = body := by
    obtain ⟨ctx,q,eq,shape⟩ := sources (ofString "main",[],body) bodyMember
    change body = compileProgExactHOLW ctx q at eq
    rw [eq]
    exact callFrontend_simp_fixed shape
  have codeRel : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
      crepToLoopCodeRelExact ctxt (globalEntryCrep pan clock globals entries).code
        (sptFromAList (compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))) := by
    apply wholeCrep_fixed_executable_codeRel _ _ (ofString "main") body
    · exact programsUnique
    · rw [first]; simp [holAlookup,body]
    · intro n ps b mem
      obtain ⟨ctx,q,eq,shape⟩ := sources (n,ps,b) mem
      simp only at eq
      rw [eq]
      exact callFrontend_simp_fixed shape
  have entry : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms pan)) 0
      (64,[],optimiseHOL (compileHOLExact ctxt .ln body)) ∈ compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan) := by
    dsimp only
    have result := firstCrep_loopEntry riscvConfig.isa (ofString "main") body rest bodyFixed
    rw [← first] at result
    obtain ⟨tail,eq⟩ := result
    rw [eq]
    simp [firstLoopName]
  exact initializedGlobal_counted_machine_fromRel pan unique sourceGood clock decs post initializers funs exns globals entries name
    program (globalEntryShapes post entries) supported layout panCtxt (globalEntryProduction post entries) value
    onlyDecls initializerShape eval compiled allocated sizeBound found relExec ranged localsWord globalShapes codeRanged codeShape
    context primitive handler exceptions fuel count postLocals postGlobals postMemory postFfi run budget
    targetTable panCodeRel varsEmpty exceptionsEmpty sources codeRel entry bitmapFits safe facts capacity

end SteppedFlapjack.Concrete
