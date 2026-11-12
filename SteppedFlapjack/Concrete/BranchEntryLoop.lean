import SteppedFlapjack.Concrete.WitnessLoopCode
import SteppedFlapjack.LoopLiveSteps.TailEntryShape

set_option maxRecDepth 10000

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps

/-- The generic `main` entry wrapper shared by all supported programs. -/
def branchingLoopEntry : HolLoopProg 64 :=
  .mark (.seq (.mark .skip) (.mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))))

/-- Two generated functions with distinct names share this optimized entry. -/
theorem twoLoopPrograms_entry_code (arch : AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) :
    (64,[],branchingLoopEntry) ∈ twoLoopPrograms arch name callee body := by
  simp only [twoLoopPrograms,List.mem_cons]
  left
  simp [firstLoopName,branchingLoopEntry,optimiseSequence,compileHOLExact,compileExpsHOLExact,
    loopNestedSeqHOL,genTemps,shrinkSequence,shrinkBranch,markAllHOL,
    crepToLoopMakeFuncsExactExecutable,twoPrograms,mkCtxtExact,makeVmapExact,findLabExact,
    HolFiniteMapExact.updateListEq,FUPDATE_LIST,FUPDATE,List.range_succ,fresh]

end SteppedFlapjack.Concrete
