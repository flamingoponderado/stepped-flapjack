import SteppedFlapjack.CrepToLoopSteps.OptimisedTailEntry
import SteppedFlapjack.LoopToWordSteps.TailEntryRiscV

/-! Shape-independent Loop-side facts for a completed Crep tail entry. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- Once a callee-specific proof supplies the optimized Loop execution, shape,
completion and bound, code lookup and clock alignment are independent of the
callee's syntax. -/
theorem branchTail_riscv_inputs_of_run {F C : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (init callee : CrepProgHOL 64) (initShape : BranchProgram init)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 C F)
    (extra : Nat) (loopPost : LoopSemStateFiniteExact 64 F) (limit : Nat)
    (initRun : evalCrepSemHOLProgExact source init = (none,middle))
    (found : middle.code.lookup name = some ([],callee))
    (complete : CompleteCrepResult result)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (loopWordRel : loopToWordStateRelHOLExact target word)
    (calleeShape : LoopSequenceSource (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln callee))
    (run : evaluate (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name []))))
      {target with clock := target.clock+extra} = (resultToLoop result,loopPost))
    (postRel : crepToLoopStateRelExact post loopPost)
    (bound : LoopSteps.steps (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name []))))
      {target with clock := target.clock+extra} ≤ limit) :
    let entry := optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))
    let compiledCallee := ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln callee
    LoopLiveSteps.SingleTailEntryShape (findLabExact ctxt name) entry ∧
    LoopSequenceSource compiledCallee ∧
    sptLookup (findLabExact ctxt name) {target with clock := target.clock+extra}.code = some ([],compiledCallee) ∧
    evaluate entry {target with clock := target.clock+extra} = (resultToLoop result,loopPost) ∧
    resultToLoop result ≠ some .error ∧ CompleteLoopResult (resultToLoop result) ∧
    loopToWordStateRelHOLExact {target with clock := target.clock+extra} {word with clock := word.clock+extra} ∧
    crepToLoopStateRelExact post loopPost ∧ LoopSteps.steps entry {target with clock := target.clock+extra} ≤ limit := by
  have foundSource : source.code.lookup name = some ([],callee) := by
    simpa only [evaluateCodeInvariantHOL init source none middle initRun] using found
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 name [] _ foundSource
  have lenZero : len = 0 := by simpa using hlen.symm
  subst len
  have label : findLabExact ctxt name = loc := by simp [findLabExact,hlab]
  have lookup : sptLookup (findLabExact ctxt name) {target with clock := target.clock+extra}.code =
      some ([],ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln callee) := by
    simpa [label,listToNumSetHOLExact] using hcode
  have shifted : loopToWordStateRelHOLExact {target with clock := target.clock+extra}
      {word with clock := word.clock+extra} := by
    rcases loopWordRel with ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    refine ⟨len,hm,hd,hs,?_,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    simp only
    omega
  exact ⟨LoopLiveSteps.optimise_singleTail
    (LoopLiveSteps.compiled_singleTail_shape ctxt live init initShape name),calleeShape,
    lookup,run,by cases complete <;> simp [resultToLoop],completeCrep_loop complete,shifted,postRel,bound⟩

end SteppedFlapjack.CrepToLoopSteps
