import SteppedFlapjack.Concrete.GeneratedMachine
import SteppedFlapjack.Concrete.NestedLoopRun
import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.Concrete.CountdownWordSpan
import SteppedFlapjack.Concrete.FixtureMachineGuards
import SteppedFlapjack.WordToStackSteps.StartRiscV
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps

/-- Executable Word table and entry frame for the nested-call witness. -/
def nestedRawWords := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
def nestedOptimizedWords := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig nestedRawWords).2
def nestedEntry : WordLangProgHOL (BitVec 64) :=
  ((sptLookup 64 (sptFromAList nestedOptimizedWords)).getD (1,.skip)).2
def nestedEntryFrame : Nat :=
  (compileProgNative riscvConfig false nestedEntry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1

/-- Native Stack code and bitmaps computed from the actual optimized table. -/
def nestedNative := compileNative riscvConfig false nestedOptimizedWords
def nestedCode : List (Nat × HolProg 64) := nestedNative.2.2.2
def nestedBitmaps : List (BitVec 64) := nestedNative.1
/-- Native frame-size table computed from the actual optimized functions. -/
def nestedFrameSizes : Spt Nat :=
  sptMapi (fun _ (argc,body) =>
    (compileProgNative riscvConfig false body argc (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1)
    (sptFromAList nestedOptimizedWords)

private theorem functionOnly_hasWordEntry (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = []) :
    ∃ entryBody, (64,1,entryBody) ∈ loopToWordCompileHOL
      (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start))) := by
  let decls := compileTopExactHOL (fs.map DeclHOL.function) start
  let programs := compileProgDeclsHOLW decls
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
  let bodyPan : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
  let crep := compileProgExactHOLW panCtxt bodyPan
  let lc := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let entryBody := loopToWordCompFuncHOL 64 [] (optimiseHOL (compileHOLExact lc .ln crep))
  refine ⟨entryBody,?_⟩
  simpa [entryBody,lc,crep,bodyPan,panCtxt,decls,programs,firstLoopName] using
    functionOnly_wordEntry fs start body found noInline riscvConfig.isa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem functionOnly_initialized_machine
    (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (rawEq : panToWordCompileProgHOL riscvConfig.isa pan =
      loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start))))
    (limit : Nat) (value : BitVec 64)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (bitmapFits : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let bitmaps := (compileNative riscvConfig false optimized).1
      0xa0020018 + bitmaps.length*8 ≤ 0xa0410000)
    (safe : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      fixtureStackSafe (compileNative riscvConfig false optimized).2.2.2 = true)
    (facts : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let code := (compileNative riscvConfig false optimized).2.2.2
      (fixtureRemoveLabels code).isSome = true ∧ (fixtureCodeBytes code).length ≤ 0xecc ∧ (fixtureCodeBytes code).length % 4 = 0)
    (capacity : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
      let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
      let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
        (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
      optionLe (optionMap₂ max (some (max 1 (1+frame)))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172))
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Unit)
    (run : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let native := compileNative riscvConfig false optimized
      let code := native.2.2.2
      let bs := native.1
      let cfg := fixtureCompilerConfig code
      WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
        {(configuredWord code optimized cfg bs) with clock := 6*limit+1} =
          (some (.result (.loc 1 0) [.word value]),wordPost))
 :
    let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
    let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
    let native := compileNative riscvConfig false optimized
    let code := native.2.2.2
    let bitmaps := native.1
    let allowance := (max 1 (wordCodeWeight (sptFromAList optimized)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bitmaps code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bitmaps) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = wordPost.ffi.ioEvents := by
  obtain ⟨entryBody,entryMember⟩ := functionOnly_hasWordEntry fs start body found noInline
  exact generated_initialized_machine (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start))
    entryBody entryMember pan unique rawEq limit value sourceGood bitmapFits safe facts capacity wordPost run

end SteppedFlapjack.Concrete
