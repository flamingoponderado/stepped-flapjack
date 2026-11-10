import SteppedFlapjack.Concrete.WordTables
import SteppedFlapjack.WordToStackSteps.BitmapFree
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.Concrete SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

namespace SteppedFlapjack.Concrete

/-- Every supported two-function scalar compiler output uses one standard bitmap word. -/
theorem twoWordTables_native_bitmaps (arch : AsmArchitecture) (name callee : MlString) (body : CrepProgHOL 64)
    (fresh : name ≠ callee) (shape : ScalarProgram body) (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64) :
    (compileNative ac false (compile wc ac (loopToWordCompileHOL (twoLoopPrograms arch name callee body))).2).1 = [4] := by
  apply bitmapFree_compileNative
  apply wholeCompile_tailOrLoop_shape
  intro row member
  rcases row with ⟨label,arity,program⟩
  have facts := twoWordTables_facts arch name callee body fresh shape
  have all := facts.2.2.2.1 label arity program member
  rcases all with loop | tail
  · exact Or.inr loop
  · exact Or.inl tail

end SteppedFlapjack.Concrete
