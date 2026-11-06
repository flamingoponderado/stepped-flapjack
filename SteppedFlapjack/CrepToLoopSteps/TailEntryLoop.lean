import SteppedFlapjack.CrepToLoopSteps.TailCallSteps

/-! Quantitative Loop simulation of a branch initializer and tail call. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A successful supported initializer followed by a completed supported
zero-argument callee has a bounded actual Loop execution. The caller-to-callee
relations are derived from the ordinary compiler relations and code lookup. -/
theorem branch_tailCall_nil_crep_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (calleeInit : CrepProgHOL 64) (calleeInitShape : BranchProgram calleeInit)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F)
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
      evaluate (compileHOLExact ctxt live (.seq init (.call none name [])))
        {target with clock := target.clock+extra} = (resultToLoop result,final) ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.seq init (.call none name [])))
        {target with clock := target.clock+extra} ≤
      4 + sizeOf (compileHOLExact ctxt live init) +
        sizeOf (ocompileHOLExact c .ln p) *
          (2 * (factor * (CrepSteps.steps p (decClockCrepSemHOL
            {middle with locals := HolFiniteMapExact.empty.updateList []})+1)) + 1) := by
  obtain ⟨firstExtra,firstResult,firstTarget,firstRun,firstState,firstMem,firstGlobals,
    firstCode,firstMap,firstLocals,_,_⟩ :=
    branchProgram_correct_with_bounded_extra init initShape source middle none target ctxt live
      initRun (by simp) stateRel memRel globalsRel codeRel localsRel
  have firstNone : firstResult = none := by simpa [resultToLoop] using firstMap
  subst firstResult
  have targetClock : firstTarget.clock ≠ 0 := by
    have h := firstState.2.2.1
    omega
  have ⟨calleeState,calleeMem,calleeGlobals,calleeCode,calleeLocals⟩ :=
    tailCall_nil_entry_relations ctxt live middle firstTarget name _ firstState firstMem firstGlobals firstCode firstLocals found
  obtain ⟨callExtra,final,callRun,finalRel,callBound⟩ :=
    compile_tailCall_nil_crep_bound ctxt live middle firstTarget name calleeInit calleeInitShape condition conditionShape
      body tail bodyShape tailShape _ post result firstCode found targetClock calleeRun complete
      calleeState calleeMem calleeGlobals calleeCode calleeLocals
  have lifted := evaluate_add_clock_eq (compileHOLExact ctxt live init)
    {target with clock := target.clock+firstExtra} none firstTarget callExtra firstRun (by simp)
  have firstLift : evaluate (compileHOLExact ctxt live init) {target with clock := target.clock+(firstExtra+callExtra)} =
      (none,{firstTarget with clock := firstTarget.clock+callExtra}) := by
    simpa [Nat.add_assoc] using lifted
  have firstBound := LoopSteps.branchedProgram_static_bound (compile_branchProgram initShape ctxt live)
    {target with clock := target.clock+(firstExtra+callExtra)}
  have count := LoopSteps.steps_seq (compileHOLExact ctxt live init) (compileHOLExact ctxt live (.call none name []))
    {target with clock := target.clock+(firstExtra+callExtra)}
  rw [firstLift] at count
  refine ⟨firstExtra+callExtra,final,?_,finalRel,?_⟩
  · rw [compileHOLExact,evaluate_seq,firstLift]
    exact callRun
  · rw [compileHOLExact]
    simp only at count
    omega

/-- The successful entry count dominates the visits of its reached callee. -/
theorem tailEntry_callee_steps_le {width : Nat} [NeZero width] {F : Type}
    (init : CrepProgHOL width) (name : MlString) (body : CrepProgHOL width)
    (source middle : CrepSemHOLState width F)
    (initRun : evalCrepSemHOLProgExact source init = (none,middle))
    (found : middle.code.lookup name = some ([],body)) (clock : middle.clock ≠ 0) :
    CrepSteps.steps body (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []}) ≤
      CrepSteps.steps (.seq init (.call none name [])) source := by
  rw [CrepSteps.steps_seq,initRun]
  simp only
  rw [CrepSteps.steps_call_tail name [] middle [] [] body (by rfl) found (by rfl) (by simp) clock]
  change CrepSteps.steps body (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []}) ≤
    1 + CrepSteps.steps init source + (1 + CrepSteps.steps body
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []}))
  omega

/-- A successful supported initializer followed by a completed supported
zero-argument callee has a bounded actual Loop execution. The caller-to-callee
relations are derived from the ordinary compiler relations and code lookup. -/
theorem branch_tailCall_nil_entry_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (calleeInit : CrepProgHOL 64) (calleeInitShape : BranchProgram calleeInit)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F)
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
      evaluate (compileHOLExact ctxt live (.seq init (.call none name [])))
        {target with clock := target.clock+extra} = (resultToLoop result,final) ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.seq init (.call none name [])))
        {target with clock := target.clock+extra} ≤
      4 + sizeOf (compileHOLExact ctxt live init) +
        sizeOf (ocompileHOLExact c .ln p) *
          (2 * (factor * (CrepSteps.steps (.seq init (.call none name [])) source+1)) + 1) := by
  obtain ⟨extra,final,run,rel,bound⟩ := branch_tailCall_nil_crep_bound ctxt live name init initShape
    calleeInit calleeInitShape condition conditionShape body tail bodyShape tailShape source middle post result target
    initRun found clock calleeRun complete stateRel memRel globalsRel codeRel localsRel
  have countLe := tailEntry_callee_steps_le init name (.seq calleeInit (.seq (.while condition body) tail)) source middle initRun found clock
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p : CrepProgHOL 64 := .seq calleeInit (.seq (.while condition body) tail)
  change CrepSteps.steps p (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []}) ≤
    CrepSteps.steps (.seq init (.call none name [])) source at countLe
  let factor := 1 + sizeOf (compileHOLExact c .ln calleeInit) +
    (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
      (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
        sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))
  have scaled : factor * (CrepSteps.steps p (decClockCrepSemHOL
      {middle with locals := HolFiniteMapExact.empty.updateList []}) + 1) ≤
      factor * (CrepSteps.steps (.seq init (.call none name [])) source + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have finalScale := Nat.mul_le_mul_left (sizeOf (ocompileHOLExact c .ln p))
    (show 2 * (factor * (CrepSteps.steps p (decClockCrepSemHOL
      {middle with locals := HolFiniteMapExact.empty.updateList []}) + 1)) + 1 ≤
      2 * (factor * (CrepSteps.steps (.seq init (.call none name [])) source + 1)) + 1 by omega)
  dsimp only [c,p,factor] at scaled finalScale
  exact ⟨extra,final,run,rel,bound.trans (by omega)⟩

end SteppedFlapjack.CrepToLoopSteps
