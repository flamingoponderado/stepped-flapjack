import SteppedFlapjack.CrepToLoopSteps.ScalarExecutable
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopLiveSteps

def twoPrograms {width : Nat} [NeZero width] (name callee : MlString) (body : CrepProgHOL width) :
    List (MlString × List Nat × CrepProgHOL width) :=
  [(name,[],.seq .skip (.call none callee [])),(callee,[],body)]

def twoLoopPrograms {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (name callee : MlString) (body : CrepProgHOL width) : List (Nat × List Nat × HolLoopProg width) :=
  let programs := twoPrograms name callee body
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  [(firstLoopName,[],optimiseSequence (compileHOLExact ctxt .ln (.seq .skip (.call none callee [])))),
   (firstLoopName+1,[],optimiseScalar (compileHOLExact ctxt .ln body))]

theorem twoLoopPrograms_eq {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (name callee : MlString) (body : CrepProgHOL width) (shape : ScalarProgram body) :
    twoLoopPrograms arch name callee body = compileProgHOLExact arch (twoPrograms name callee body) := by
  let programs := twoPrograms name callee body
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  have calleeShape : ScalarLoop (compileHOLExact ctxt .ln body) := compile_scalar_program shape ctxt .ln
  have entryShape := (compiled_tailEntry_shape ctxt .ln (.skip : CrepProgHOL width) (.expr (.leaf .skip)) callee).1
  have a := optimiseSequence_tail_eq entryShape
  have b := optimiseScalar_eq calleeShape
  simpa [twoLoopPrograms,twoPrograms,compileProgHOLExact,compFuncHOLExact,
    crepSimpProgHOL,scalarProgram_simp_fixed shape,programs,ctxt,Nat.add_comm,List.range_succ,listToNumSetHOLExact] using And.intro a b
end SteppedFlapjack.CrepToLoopSteps
