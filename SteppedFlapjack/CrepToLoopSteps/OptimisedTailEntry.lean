import SteppedFlapjack.CrepToLoopSteps.TailEntryLoop
import SteppedFlapjack.LoopLiveSteps.TailEntryShape
import SteppedFlapjack.LoopLiveSteps.TailEntryGlobalBound

/-! Actual optimizer execution for a source-bounded tail entry. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A successful supported entry has an optimized Loop execution and a Word
tail-entry shape. The visit bound in this theorem applies to the unoptimized
Loop entry; the following theorem bounds the optimized entry. -/
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

/-- A successful supported entry has an actual optimized Loop execution and
an explicit Crep-visit bound, with the real Word tail-entry shape. -/
theorem branch_tailCall_nil_optimised_bound {F : Type}
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
      LoopSteps.steps (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name []))))
        {target with clock := target.clock+extra} ≤
      (sizeOf (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))) + sizeOf (ocompileHOLExact c .ln p)) *
        (2 * (4 + sizeOf (compileHOLExact ctxt live init) +
          sizeOf (ocompileHOLExact c .ln p) *
            (2 * (factor * (CrepSteps.steps (.seq init (.call none name [])) source+1)) + 1)) + 1) := by
  obtain ⟨extra,final,run,rel,bound⟩ := branch_tailCall_nil_entry_bound ctxt live name init initShape
    calleeInit calleeInitShape condition conditionShape body tail bodyShape tailShape source middle post result target
    initRun found clock calleeRun complete stateRel memRel globalsRel codeRel localsRel
  have shape := LoopLiveSteps.compiled_singleTail_shape ctxt live init initShape name
  have codeEq := evaluateCodeInvariantHOL init source none middle initRun
  have foundSource : source.code.lookup name = some ([],.seq calleeInit (.seq (.while condition body) tail)) := by
    simpa only [codeEq] using found
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 name [] _ foundSource
  have lenZero : len = 0 := by simpa using hlen.symm
  subst len
  have label : findLabExact ctxt name = loc := by simp [findLabExact,hlab]
  have calleeShape := LoopLiveSteps.optimise_sequence
    (branchConditionWhileBranch_wordSimpShape calleeInit calleeInitShape condition conditionShape
      body tail bodyShape tailShape (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln)
  have code : LoopLiveSteps.TailCodeBound {target with clock := target.clock+extra}.code
      (findLabExact ctxt name)
      (sizeOf (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
        (.seq calleeInit (.seq (.while condition body) tail)))) := by
    intro callee lookup
    rw [label] at lookup
    have eq : callee = ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
        (.seq calleeInit (.seq (.while condition body) tail)) := by
      have h := Option.some.inj (lookup.symm.trans hcode)
      exact (Prod.mk.inj h).2
    subst callee
    exact ⟨by simpa only [ocompileHOLExact] using calleeShape, le_rfl⟩
  obtain ⟨optRun,optShape,optBound⟩ := LoopLiveSteps.optimise_tailEntry_source_bound shape
    {target with clock := target.clock+extra} final (resultToLoop result) _ code run (completeCrep_loop complete)
  have wordShape := LoopLiveSteps.tailEntry_word (LoopLiveSteps.singleTail_to_tail optShape) wordCtxt labels
  refine ⟨extra,final,optRun,wordShape,rel,?_⟩
  exact optBound.trans (Nat.mul_le_mul_left _ (by omega))

end SteppedFlapjack.CrepToLoopSteps
