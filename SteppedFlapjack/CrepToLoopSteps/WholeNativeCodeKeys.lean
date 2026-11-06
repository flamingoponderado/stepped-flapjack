import SteppedFlapjack.CrepToLoopSteps.NativeTailFrontendSetup
import SteppedFlapjack.WordToStackSteps.NativeCodeKeys

/-! Distinct native Stack names from the actual Crep compiler output. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

/-- The whole Crep-to-native compiler produces a Stack code list with unique
keys, including its runtime stubs. -/
theorem wholeCrep_native_code_nodup (arch : AsmArchitecture)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64) :
    (((compileNative ac false (compile wc ac
      (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2).map Prod.fst).Nodup := by
  let programs := loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)
  have nodup : (programs.map Prod.fst).Nodup :=
    loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact arch _)
  have minimum : ∀ entry ∈ programs, 60 ≤ entry.1 := by
    apply LoopToWord.loop_to_word_compile_lab_min _ _ 60
    exact ⟨rfl,crep_to_loop_compile_prog_lab_min arch _ _ rfl⟩
  have noRaise : raiseStubLocation ∉ programs.map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [raiseStubLocation,wordNumStubs,stackNumStubs] at lower
  have noStore : storeConstsStubLocation ∉ programs.map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [storeConstsStubLocation,wordNumStubs,stackNumStubs] at lower
  have names : ((compile wc ac programs).2.map Prod.fst) = programs.map Prod.fst := wholeCompile_names wc ac programs
  change (((compileNative ac false (compile wc ac programs).2).2.2.2).map Prod.fst).Nodup
  apply compileNative_code_nodup
  · rw [names]; exact nodup
  · rw [names]; exact noRaise
  · rw [names]; exact noStore

end SteppedFlapjack.CrepToLoopSteps
