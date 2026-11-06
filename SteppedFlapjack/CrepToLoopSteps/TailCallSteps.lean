import SteppedFlapjack.CrepToLoopSteps.InlineEntry
import SteppedFlapjack.LoopSteps.Defs
import SteppedFlapjack.LoopLiveSteps.Consumption
import Flapjack.Pancake.CrepToLoop.StateRel
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.WordSimpSequence
import SteppedFlapjack.CrepToLoopSteps.BackendReady

/-! Source-shaped bounds for compiled zero-argument Crep tail calls. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The exact Crep compiler emits one Loop call, in its nested-sequence
wrapper, for a zero-argument tail call. -/
theorem compile_tailCall_nil {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString) :
    compileHOLExact ctxt live (.call none name [] : CrepProgHOL width) =
      .seq (.call none (some (findLabExact ctxt name)) [] none) .skip := by
  simp [compileHOLExact,compileExpsHOLExact,genTemps,loopNestedSeqHOL]

/-- The code relation identifies the exact optimized zero-argument callee and
the Loop compiler's numeric call target. -/
theorem tailCall_nil_lookup {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) :
    findCode (some (findLabExact ctxt name)) [] target.code =
      some (.ln,ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body) := by
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 name [] body found
  have lenZero : len = 0 := by simpa using hlen.symm
  subst len
  have label : findLabExact ctxt name = loc := by simp [findLabExact,hlab]
  rw [label]
  simp [findCode,hcode,sptFromAList]

/-- A successful compiled zero-argument tail call visits the actual optimized
callee, with at most two extra Loop wrapper nodes. -/
theorem compile_tailCall_nil_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) (clock : target.clock ≠ 0) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) target ≤
      3 + LoopSteps.steps (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
        {decClock target with locals := .ln} := by
  have lookup := tailCall_nil_lookup ctxt source target name body codeRel found
  have call := LoopSteps.steps_call_tail (some (findLabExact ctxt name)) [] target [] .ln
    (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
    (by rfl) lookup clock
  rw [compile_tailCall_nil,LoopSteps.steps_seq,call]
  rcases run : evaluate (.call none (some (findLabExact ctxt name)) [] none) target with ⟨out,post⟩
  cases out with
  | none =>
    simp only
    have leaf : LoopSteps.steps (.skip : HolLoopProg width) post = 1 := LoopSteps.steps_leaf _ _ rfl
    omega
  | some result => simp only; omega

/-- A completed supported callee execution gives a source-visit bound for its
actual optimized Loop tail call, with a constant call-wrapper overhead. -/
theorem compile_tailCall_nil_optimised_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState 64 F)
    (target final : LoopSemStateFiniteExact 64 F) (name : MlString) (body : CrepProgHOL 64)
    (result : Option (LoopResultExact 64)) (limit : Nat)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) (clock : target.clock ≠ 0)
    (shape : SteppedFlapjack.LoopToWordSteps.LoopSequenceSource
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body))
    (run : evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} = (result,final))
    (complete : SteppedFlapjack.LoopToWordSteps.CompleteLoopResult result)
    (sourceBound : LoopSteps.steps (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} ≤ limit) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) target ≤
      3 + sizeOf (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body) * (2 * limit + 1) := by
  have callBound := compile_tailCall_nil_steps ctxt live source target name body codeRel found clock
  obtain ⟨_,_,optBound⟩ := LoopLiveSteps.optimise_complete_source_steps shape
    {decClock target with locals := .ln} final result run complete
  have scaled := Nat.mul_le_mul_left
    (sizeOf (optimiseHOL (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)))
    (show 2 * LoopSteps.steps (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} + 1 ≤ 2 * limit + 1 by omega)
  unfold ocompileHOLExact at callBound ⊢
  omega

/-- A supported completed Crep callee bounds the actual optimized Loop tail
call, after the proved compiler clock extension, by its Crep visits. -/
theorem compile_tailCall_nil_crep_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (callerSource : CrepSemHOLState 64 F)
    (target : LoopSemStateFiniteExact 64 F) (name : MlString)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (codeRel : crepToLoopCodeRelExact ctxt callerSource.code target.code)
    (found : callerSource.code.lookup name = some ([],.seq init (.seq (.while condition body) tail)))
    (clock : target.clock ≠ 0)
    (run : evalCrepSemHOLProgExact source (.seq init (.seq (.while condition body) tail)) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source {decClock target with locals := .ln})
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (calleeCodeRel : crepToLoopCodeRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) source.code target.code)
    (localsRel : crepToLoopLocalsRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln source.locals .ln) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := .seq init (.seq (.while condition body) tail)
    let factor := 1 + sizeOf (compileHOLExact c .ln init) +
      (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
          sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))
    ∃ extra final,
      evaluate (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} =
        (resultToLoop result,final) ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} ≤
        3 + sizeOf (ocompileHOLExact c .ln p) * (2 * (factor * (CrepSteps.steps p source+1)) + 1) := by
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p : CrepProgHOL 64 := .seq init (.seq (.while condition body) tail)
  let entry : LoopSemStateFiniteExact 64 F := {decClock target with locals := .ln}
  obtain ⟨extra,final,loopRun,postRel,_,_,_,_,loopBound⟩ :=
    branchConditionWhileBranch_programBound init initShape condition conditionShape body tail bodyShape tailShape c .ln
      source post result entry run (completeCrep_nonerror complete) stateRel memRel globalsRel calleeCodeRel localsRel
  have shift : ({decClock {target with clock := target.clock+extra} with locals := .ln} : LoopSemStateFiniteExact 64 F) =
      {entry with clock := entry.clock+extra} := by
    simp only [entry,decClock]
    congr 1
    omega
  have extendedRun : evaluate (compileHOLExact c .ln p) {decClock {target with clock := target.clock+extra} with locals := .ln} =
      (resultToLoop result,final) := by rw [shift]; exact loopRun
  have extendedBound : LoopSteps.steps (compileHOLExact c .ln p) {decClock {target with clock := target.clock+extra} with locals := .ln} ≤
      (1 + sizeOf (compileHOLExact c .ln init) +
        (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
            sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))) * (CrepSteps.steps p source+1) := by
    rw [shift]; exact loopBound
  have codeRel' : crepToLoopCodeRelExact ctxt callerSource.code {target with clock := target.clock+extra}.code := codeRel
  have optimizedRun := (LoopLiveSteps.optimise_complete_source_steps
    (branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape c .ln)
    {decClock {target with clock := target.clock+extra} with locals := .ln} final (resultToLoop result)
    extendedRun (completeCrep_loop complete)).1
  have callLookup := tailCall_nil_lookup ctxt callerSource {target with clock := target.clock+extra} name p codeRel' found
  have compiledRun : evaluate (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} =
      (resultToLoop result,final) := by
    rw [compile_tailCall_nil,evaluate_seq]
    have callRun : evaluate (.call none (some (findLabExact ctxt name)) [] none) {target with clock := target.clock+extra} =
        (resultToLoop result,final) := by
      rw [evaluate]
      simp only [show getVars [] {target with clock := target.clock+extra} = some [] from rfl,
        callLookup,Option.isSome_none,Bool.false_eq_true,if_false]
      have nz : target.clock + extra ≠ 0 := by omega
      simp only [nz, dite_false]
      simp only [ocompileHOLExact]
      rw [optimizedRun]
      cases complete <;> rfl
    rw [callRun]
    cases complete <;> rfl
  refine ⟨extra,final,compiledRun,postRel,?_⟩
  exact compile_tailCall_nil_optimised_bound ctxt live callerSource {target with clock := target.clock+extra} final name p
    (resultToLoop result) _ codeRel' found (by simp; omega)
    (branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape c .ln)
    extendedRun (completeCrep_loop complete) extendedBound

end SteppedFlapjack.CrepToLoopSteps
