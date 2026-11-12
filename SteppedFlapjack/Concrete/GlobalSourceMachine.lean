import SteppedFlapjack.Concrete.GlobalConfiguredWord
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

/-- The actual Crep table selected by the source-to-Word compiler. -/
def globalSourcePrograms (pan : List (DeclHOL 64)) : List (MlS × List Nat × CrepProgHOL 64) :=
  compileProgDeclsHOLW (compileTopExactHOL
    (Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL pan)) (ofString "main"))
def globalSourceRaw (pan : List (DeclHOL 64)) := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))
def globalSourceWords (pan : List (DeclHOL 64)) := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (globalSourceRaw pan)).2
def globalSourceNative (pan : List (DeclHOL 64)) := compileNative riscvConfig false (globalSourceWords pan)
def globalSourceCode (pan : List (DeclHOL 64)) := (globalSourceNative pan).2.2.2
def globalSourceBitmaps (pan : List (DeclHOL 64)) := (globalSourceNative pan).1
def globalSourceEntry (pan : List (DeclHOL 64)) : WordLangProgHOL (BitVec 64) :=
  ((sptLookup 64 (sptFromAList (globalSourceWords pan))).getD (1,.skip)).2
def globalSourceFrame (pan : List (DeclHOL 64)) : Nat :=
  (compileProgNative riscvConfig false (globalSourceEntry pan) 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
def globalSourceFrames (pan : List (DeclHOL 64)) : Spt Nat :=
  sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList (globalSourceWords pan))

private theorem bitmapFits_sourceBase (n : Nat) (h : 0xa0020018 + n*8 ≤ 0xa0410000) :
    0xa0020018 + n*8 ≤ sourceBase := by
  simp only [sourceBase]
  omega

/-- A successful global-aware source run reaches the actual initialized
    RISC-V compilation at an explicit program- and configuration-derived bound. -/
theorem globalSource_machine
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (globals : PanGlobalsContextExact 64) (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : GlobalCallFrontend globals panCtxt p)
    (source sourceFinal panTarget : PanSemStateFiniteExact 64 Unit) (value : BitVec 64)
    (crep : CrepSemHOLState 64 Unit) (sourceLimit : Nat)
    (sourceTable : GlobalCallTable globals source.code)
    (compiledTable : crep.code = alistToFmapCodeExact (globalSourcePrograms pan))
    (targetTable : CallFrontendCode panCtxt panTarget.code)
    (run : source.evaluateHOLFiniteState p = (some (.returned (.val (.word value))),sourceFinal))
    (sourceBound : controlSteps p source ≤ sourceLimit)
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
    (entry : let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
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
    let limit := globalProgramOptLimit globals panCtxt p crep (globalSourcePrograms pan) sourceLimit ref ctxt .ln
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
  let limit := globalProgramOptLimit globals panCtxt p crep programs sourceLimit ref ctxt .ln
  have rawEq : panToWordCompileProgHOL riscvConfig.isa pan = raw := by rfl
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have good : StackToLab.Proofs.GoodCode.goodCode 24 code := by
    have h := source_nativeGoodCode pan unique
    rw [rawEq, ← phase3WordConfig_eq] at h
    simpa [code,globalSourceCode,globalSourceNative,words,globalSourceWords,compileWith_eq_compile _ allocator] using h
  have fits : 0xa0020018 + bs.length*8 ≤ sourceBase := bitmapFits_sourceBase bs.length bitmapFits
  obtain ⟨wordPost,wordRun,wordFfi⟩ := globalConfiguredWord globals panCtxt p shape source sourceFinal panTarget value
    crep programs sourceLimit sourceTable compiledTable targetTable run sourceBound globalRel panCrepRel panCodeRel
    excpRel panLocalsRel sources ref ctxt ctxtVars crepGlobals crepLocals codeRel heap memDomain sharedDomain base byteOrder ffi
    cfg entry fits good sourceMemory
  let body := compileProgExactHOLW panCtxt (compileProgExactHOL globals p)
  let optimized := optimiseHOL (compileHOLExact ctxt .ln body)
  let wordCtxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL (sptDifference (accVarsHOL optimized .ln) (LoopToWord.toNumSetHOL []))) .ln
  have member : (64,1,(LoopToWord.compHOL wordCtxt optimized (64,2)).1) ∈ raw := by
    apply List.mem_map.mpr
    exact ⟨(64,[],optimized),entry,by simp [loopToWordCompFuncHOL,wordCtxt]⟩
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := generated_initialized_machine programs _ member pan unique rawEq limit value
    sourceGood bitmapFits safe facts capacity wordPost wordRun
  exact ⟨finalMachine,finalFfi,machineRun,events.trans (congrArg (fun f => f.ioEvents) wordFfi.symm)⟩
end SteppedFlapjack.Concrete
