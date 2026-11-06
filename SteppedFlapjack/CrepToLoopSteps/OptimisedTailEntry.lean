import SteppedFlapjack.CrepToLoopSteps.TailEntryLoop
import SteppedFlapjack.LoopLiveSteps.TailEntryShape

/-! Actual optimizer execution for a source-bounded tail entry. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A successful supported entry has an optimized Loop execution and a Word
tail-entry shape. The visit bound applies to the unoptimized Loop entry; a
bound on the optimizer's own visits remains to be proved. -/
theorem branch_tailCall_nil_optimised_execution {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (calleeInit : CrepProgHOL 64) (calleeInitShape : BranchProgram calleeInit)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F) (wordCtxt : Spt Nat) (labels : Nat × Nat)
    (initRun : evalCrepSemHOLProgExact source init = (none,middle))
    (found : middle.code.lookup name = some ([],.seq calleeInit (.seq (.while condition body) tail)))
    (clock : middle.clock ≠ 0)
    (calleeRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []})
      (.seq calleeInit (.seq (.while condition body) tail)) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := .seq calleeInit (.seq (.while condition body) tail)
    let factor := 1 + sizeOf (compileHOLExact c .ln calleeInit) +
      (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
          sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))
    ∃ extra final,
      evaluate (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name []))))
        {target with clock := target.clock+extra} = (resultToLoop result,final) ∧
      LoopLiveSteps.WordTailEntryShape (LoopToWord.compHOL wordCtxt
        (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))) labels).1 ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.seq init (.call none name [])))
        {target with clock := target.clock+extra} ≤
      4 + sizeOf (compileHOLExact ctxt live init) +
        sizeOf (ocompileHOLExact c .ln p) *
          (2 * (factor * (CrepSteps.steps (.seq init (.call none name [])) source+1)) + 1) := by
  obtain ⟨extra,final,run,rel,bound⟩ := branch_tailCall_nil_entry_bound ctxt live name init initShape
    calleeInit calleeInitShape condition conditionShape body tail bodyShape tailShape source middle post result target
    initRun found clock calleeRun complete stateRel memRel globalsRel codeRel localsRel
  have optimized := LoopLiveSteps.compiled_tailEntry_optimise_correct ctxt live init initShape name
    {target with clock := target.clock+extra} final (resultToLoop result) wordCtxt labels run (completeCrep_loop complete)
  exact ⟨extra,final,optimized.1,optimized.2,rel,bound⟩

end SteppedFlapjack.CrepToLoopSteps
