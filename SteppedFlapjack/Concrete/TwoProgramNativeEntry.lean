import SteppedFlapjack.Concrete.CountdownStackSpan
import SteppedFlapjack.Concrete.WordTables
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.WordAllocSteps.CompiledCodeTail
import Flapjack.Compiler.Backend.RegAlloc.Executable
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
namespace SteppedFlapjack.Concrete

/-- The compiler emits the same direct-tail entry for each scalar witness. -/
theorem twoProgram_optimizedEntry_lookup (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) (shape : ScalarProgram body) :
    let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
    sptLookup 64 (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2) = some (1,countdownOptimizedEntry) := by
  let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
  have table := twoWordTables_facts arch name callee body fresh shape
  have loopEq := (twoLoopPrograms_eq arch name callee body shape).symm
  have mem : (64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry) ∈ programs := by
    simpa [programs,loopEq] using table.1
  have unique : (programs.map Prod.fst).Nodup := by simpa [programs,loopEq] using table.2.2.1
  have lookup := (wholeCompile_entry_lookups countdownRiscVBackend.wordToWordConf riscvConfig programs 64 1 _ mem unique).2
  have color : entryColour countdownRiscVBackend.wordToWordConf programs 64 = none := by rfl
  have entry : loopToWordCompFuncHOL 64 [] branchingLoopEntry = .seq .skip (.seq (.call none (some 65) [0] none) .skip) := by with_unfolding_all rfl
  rw [color,entry] at lookup
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have opt : (fullCompileSingle riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
      ((64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),none)).2.2 = countdownOptimizedEntry := by
    rw [← fullCompileSingleExecutable_eq]
    have h := countdown_entry_optimized
    rw [allocator] at h
    exact congrArg (fun row => row.2.2) h
  change sptLookup 64 (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2) =
    some (1,(fullCompileSingle riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
      ((64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),none)).2.2) at lookup
  rw [opt] at lookup
  exact lookup

/-- That optimized entry uses a zero-sized native frame. -/
theorem twoProgram_optimizedEntry_frame (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) (shape : ScalarProgram body)
    (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config) :
    let words := (compile countdownRiscVBackend.wordToWordConf riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body)))).2
    sptLookup 64 (fixtureWord code words cfg).stackSize = some 0 := by
  change sptLookup 64 (sptMapi _ (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig
    (loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body)))).2)) = _
  rw [sptLookupMapi,twoProgram_optimizedEntry_lookup arch name callee body fresh shape]
  simp only [Option.map_some]
  rw [nativeEntryFrameSize_compile]
  with_unfolding_all rfl
/-- The actual optimized callee of a scalar fixture is a flat loop block. -/
theorem twoProgram_optimizedCallee (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) (shape : ScalarProgram body) :
    let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
    let code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2
    WordProps.noInstallCode code ∧ RegTailLocalCode countdownOptimizedEntry code := by
  let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
  let code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2
  let calleeWord := loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body)
  let out := (fullCompileSingle riscvConfig.twoRegArith countdownZeroLimit countdownRiscVBackend.wordToWordConf.regAlg riscvConfig
    ((65,1,calleeWord),entryColour countdownRiscVBackend.wordToWordConf programs 65)).2.2
  have facts := twoWordTables_facts arch name callee body fresh shape
  have loopEq := (twoLoopPrograms_eq arch name callee body shape).symm
  have mem : (65,1,calleeWord) ∈ programs := by simpa [programs,calleeWord,loopEq] using facts.2.1
  have nodup : (programs.map Prod.fst).Nodup := by simpa [programs,loopEq] using facts.2.2.1
  have shapes : TailProgramShapes programs := by simpa [programs,loopEq] using facts.2.2.2.1
  have wordShape : LoopSequence calleeWord := by simpa [calleeWord] using facts.2.2.2.2.2.1
  have lookup : sptLookup 65 code = some (1,out) := by
    simpa [code,out,countdownZeroLimit,RowColoring.limit] using
      (wholeCompile_entry_lookups countdownRiscVBackend.wordToWordConf riscvConfig programs 65 1 calleeWord mem nodup).2
  have relations := wholeCompile_tail_codeRelations countdownRiscVBackend.wordToWordConf riscvConfig programs shapes
  have outShape : LoopSequence out := by
    dsimp only [out]
    rw [fullCompileSingle_eq_alloc riscvConfig riscvConfig.twoRegArith 1 65 countdownRiscVBackend.wordToWordConf.regAlg countdownZeroLimit _ wordShape]
    simpa only using wordAlloc_loopSequence 65 riscvConfig countdownRiscVBackend.wordToWordConf.regAlg countdownZeroLimit _ (preAlloc_shape riscvConfig riscvConfig.twoRegArith 1 wordShape)
  have flat : flatExpConventions out = true :=
    codeRel_target_flat _ _ relations.2.2.1 relations.2.2.2.1 65 1 out lookup
  refine ⟨relations.2.2.2.2.1,?_⟩
  intro loc call
  cases call with
  | left h => cases h
  | right h => cases h; exact ⟨1,out,lookup,flat_loopSequence_block outShape flat⟩

end SteppedFlapjack.Concrete
