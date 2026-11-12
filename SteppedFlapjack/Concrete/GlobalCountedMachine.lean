import SteppedFlapjack.Concrete.GlobalSourceMachine
import SteppedFlapjack.Concrete.GlobalFrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- A terminating counted executable source run reaches the compiled RISC-V machine
with a bound computed from its code, configuration, and initial source clock. -/
theorem globalCountedSource_machine
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (globals : PanGlobalsContextExact 64) (panCtxt : PanToCrepContextExact 64)
    (program : Prog (RiscV.Word 64)) (shapes : VarName → Option ShapeHOL)
    (supported : Supported shapes program)
    (layout : GlobalLayout shapes globals)
    (source panTarget : PanSemStateFiniteExact 64 Unit) [DecidablePred source.memaddrs]
    (production : PanSemState (RiscV.Word 64) (FfiState Unit)) (value : BitVec 64)
    (productionRel : PanSemStateRelExec production source.toExact)
    (productionRanged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
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
    (budget : count ≤ source.clock) (crep : CrepSemHOLState 64 Unit)
    (compiledTable : crep.code = alistToFmapCodeExact (globalSourcePrograms pan))
    (targetTable : CallFrontendCode panCtxt panTarget.code)
    (globalRel : panGlobalsStateRelHOLExact true globals source panTarget)
    (panCrepRel : panToCrepStateRelFiniteExact panTarget crep)
    (panCodeRel : codeRelExactHOLW panCtxt panTarget.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact panCtxt.eids panTarget.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact panCtxt panTarget.locals crep.locals)
    (sources : ∀ row ∈ globalSourcePrograms pan, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (ref ctxt : CrepToLoopContextExact) (ctxtVars : ctxt.vars = HolFiniteMapExact.empty)
    (crepGlobals : crep.globals = HolFiniteMapExact.empty) (crepLocals : crep.locals = HolFiniteMapExact.empty)
    (codeRel : crepToLoopCodeRelExact ctxt crep.code (sptFromAList (compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))))
    (heap : crep.topAddr = crep.baseAddr + 2 * fixtureHeapLength)
    (memDomain : crep.memaddrs = ordinaryAddress) (sharedDomain : crep.shMemaddrs = sharedAddress)
    (base : crep.baseAddr = heapBase) (byteOrder : crep.be = false) (ffi : crep.ffi = sourceFfi)
    (entry : let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals (progToHOL program))
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
    let limit := globalProgramOptLimit globals panCtxt (progToHOL program) crep (globalSourcePrograms pan) source.clock ref ctxt .ln
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ sourceFinal : PanSemStateFiniteExact 64 Unit, ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel postFfi sourceFinal.ffi := by
  have sourceTable := globalSupported_sourceTable shapes globals layout production source productionRel codeShape
  have shape : GlobalCallFrontend globals panCtxt (progToHOL program) :=
    globalCallSupported_frontend layout supported.1 panCtxt (by intro name member; simp at member)
  obtain ⟨holResult,sourceFinal,holRun,outcome,sourceBound,_,_⟩ :=
    globalSupportedCalls_counted_source supported.1 production source productionRel productionRanged words globalShapes
      supported.2 codeRanged codeShape context primitive handler exceptions fuel count _ run budget
  cases outcome with
  | returned _ _ _ _ word final rel ranged words =>
    have bound : controlSteps (progToHOL program) source ≤ source.clock := by
      simp only [countedErrorBonus,Nat.add_zero] at sourceBound
      omega
    obtain ⟨finalMachine,finalFfi,machine,events⟩ :=
      globalSource_machine pan unique sourceGood globals panCtxt (progToHOL program) shape source sourceFinal panTarget value
        crep source.clock sourceTable compiledTable targetTable holRun bound globalRel panCrepRel panCodeRel excpRel
        panLocalsRel sources ref ctxt ctxtVars crepGlobals crepLocals codeRel heap memDomain sharedDomain base byteOrder
        ffi entry bitmapFits safe facts capacity sourceMemory
    exact ⟨sourceFinal,finalMachine,finalFfi,machine,events,rel.2.2.2.2.2.2.2.2.2.2.1⟩
end SteppedFlapjack.Concrete
