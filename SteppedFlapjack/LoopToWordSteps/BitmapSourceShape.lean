import SteppedFlapjack.LoopToWordSteps.WordSimpSequence
import SteppedFlapjack.LoopLiveSteps.TailEntryShape
import SteppedFlapjack.WordAllocSteps.TailShape
import SteppedFlapjack.WordToStackSteps.BitmapFree

/-! Static bitmap behavior from supported Loop function shapes. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps

/-- Loop-to-Word preserves the supported tail-entry and loop shapes for every
function in the program, with its actual generated context and labels. -/
theorem loopProgram_bitmapShapes {width : Nat} [NeZero width]
    (programs : List (Nat × List Nat × HolLoopProg width))
    (shapes : ∀ row ∈ programs, TailEntryShape row.2.2 ∨ LoopSequenceSource row.2.2) :
    ∀ row ∈ loopToWordCompileHOL programs, WordTailEntryShape row.2.2 ∨ LoopSequence row.2.2 := by
  intro row member
  simp only [loopToWordCompileHOL,loopToWordCompileProgHOL,List.mem_map] at member
  obtain ⟨⟨name,params,body⟩,hin,rfl⟩ := member
  have shape := shapes (name,params,body) hin
  unfold loopToWordCompFuncHOL
  rcases shape with tail | loop
  · exact Or.inl (tailEntry_word tail _ _)
  · exact Or.inr (loopSequenceSource_word loop _ _)

/-- The actual Word and native compilation of a program in this Loop fragment
emits only the initial bitmap, with no execution assumptions. -/
theorem loopProgram_native_singleBitmap {width : Nat} [NeZero width]
    (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × List Nat × HolLoopProg width))
    (shapes : ∀ row ∈ programs, TailEntryShape row.2.2 ∨ LoopSequenceSource row.2.2) :
    (WordToStack.Native.compileNative ac false (WordToWord.compile wc ac (loopToWordCompileHOL programs)).2).1 = [4] := by
  apply SteppedFlapjack.WordToStackSteps.bitmapFree_compileNative
  exact SteppedFlapjack.WordAllocSteps.wholeCompile_tailOrLoop_shape wc ac _ (loopProgram_bitmapShapes programs shapes)

end SteppedFlapjack.LoopToWordSteps
