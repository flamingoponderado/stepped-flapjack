import SteppedFlapjack.Concrete.GlobalStructNativeFacts
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem globalStruct_sourceUnique : ((functionsHOL globalStructProgram).map Prod.fst).Nodup := by
  simp [globalStructProgram,globalStructDecl,functionsHOL,ofString]
theorem globalStruct_rawWords : panToWordCompileProgHOL riscvConfig.isa globalStructProgram = globalStructActualWordPrograms := by
  unfold panToWordCompileProgHOL globalStructActualWordPrograms globalStructCallPrograms
  rw [globalStruct_simp_fixed]
  dsimp only
  rw [globalStruct_structs_fixed]
theorem globalStruct_nativeGood : StackToLab.Proofs.GoodCode.goodCode 24 globalStructNativeCode := by
  have h := source_nativeGoodCode globalStructProgram globalStruct_sourceUnique
  rw [globalStruct_rawWords, ← phase3WordConfig_eq] at h
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  simpa [globalStructNativeCode,globalStructOptimizedWords,compileWith_eq_compile _ allocator] using h
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
def globalStructNativeBitmaps := (Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false globalStructOptimizedWords).1
theorem globalStruct_bitmapFits : 0xa0020018 + globalStructNativeBitmaps.length * 8 ≤ sourceBase := by
  change 0xa0020018 + (Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false globalStructOptimizedWords).1.length * 8 ≤ sourceBase
  rw [globalStruct_nativeBitmap]
  decide
theorem globalStruct_nativeMemoryRel (cfg : LabToTarget.Config) :
    crepToLoopMemRelHOLExact globalStructCallCrep.memory (configuredStack globalStructNativeCode cfg globalStructNativeBitmaps).memory globalStructCallCrep.memaddrs := by
  have h := configuredStack_sourceMemory globalStructNativeCode cfg globalStructNativeBitmaps globalStruct_bitmapFits globalStruct_nativeGood
  have bitmaps : globalStructNativeBitmaps = [4] := globalStruct_nativeBitmap
  rw [bitmaps] at h
  simpa [globalStructCallCrep,concreteDeclCrepState,globalStructCallPan,globalStructTarget,sourceTemplateFor_one,bitmaps] using h
theorem globalStruct_frameLookup (cfg : LabToTarget.Config) :
    sptLookup 64 (configuredWord globalStructNativeCode globalStructOptimizedWords cfg globalStructNativeBitmaps).stackSize = some globalStructNativeEntryFrame := by
  rw [globalStruct_nativeEntryFrame]
  change sptLookup 64 globalStructNativeFrameSizes = some 0
  rw [globalStruct_nativeFrames]
  simp [sptLookup_sptFromAList,sptAListLookup]
theorem globalStruct_configuredWordRun (cfg : LabToTarget.Config) :
    (WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none)
      {(configuredWord globalStructNativeCode globalStructOptimizedWords cfg globalStructNativeBitmaps) with clock := 6*globalStructActualOptimizedLimit+1}).1 =
      some (.result (.loc 1 0) [.word 8]) := by
  let template := configuredWord globalStructNativeCode globalStructOptimizedWords cfg globalStructNativeBitmaps
  let memory := (configuredStack globalStructNativeCode cfg globalStructNativeBitmaps).memory
  have h := (globalStruct_actualWord_run_withMemory template globalStructNativeEntryFrame memory (globalStruct_nativeMemoryRel cfg)).1
  have starter := configuredStarter_general globalStructActualClockedCrep
    (by simp [globalStructActualClockedCrep,globalStructCallCrep,concreteDeclCrepState,globalStructCallPan,globalStructTarget,sourceTemplate])
    (by simp [globalStructActualClockedCrep,globalStructCallCrep,concreteDeclCrepState,globalStructCallPan,globalStructTarget,sourceTemplate])
    (by simp [globalStructActualClockedCrep,globalStructCallCrep,concreteDeclCrepState,globalStructCallPan,globalStructTarget,sourceTemplate])
    (by simp [globalStructActualClockedCrep,globalStructCallCrep,concreteDeclCrepState,globalStructCallPan,globalStructTarget,sourceTemplate])
    (by simp [globalStructActualClockedCrep,globalStructCallCrep,concreteDeclCrepState,globalStructCallPan,globalStructTarget,sourceTemplate])
    globalStructCallPrograms globalStructNativeCode globalStructOptimizedWords cfg globalStructNativeBitmaps globalStruct_bitmapFits globalStruct_nativeGood
    globalStructNativeEntryFrame (6*globalStructActualOptimizedLimit+1) (globalStruct_frameLookup cfg)
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have codeEq : template.code = sptFromAList (compile phase3WordConfig riscvConfig globalStructActualWordPrograms).2 := by
    simp [template,configuredWord,makeInit,globalStructOptimizedWords,compileWith_eq_compile _ allocator]
  rw [← codeEq] at h
  change (WordSemStateFiniteExact.evaluate _ {(phase3Starter riscvConfig.isa globalStructActualClockedCrep globalStructCallPrograms template fixtureHeapLength firstLoopName globalStructNativeEntryFrame) with memory := memory, clock := 6*globalStructActualOptimizedLimit+1, code := template.code}).1 = _ at h
  rw [show firstLoopName = 64 by rfl] at h
  rw [starter] at h
  exact h

end SteppedFlapjack.Concrete
