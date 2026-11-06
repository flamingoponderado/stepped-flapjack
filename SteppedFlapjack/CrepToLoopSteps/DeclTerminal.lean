import SteppedFlapjack.CrepToLoopSteps.BranchPrefix
import SteppedFlapjack.CrepToLoopSteps.DirectExpressionEval
import SteppedFlapjack.CrepToLoopSteps.WordSimpSequence
import SteppedFlapjack.LoopLiveSteps.Consumption
import SteppedFlapjack.CrepToLoopSteps.BackendReady
import SteppedFlapjack.CrepToLoopSteps.TailEntryLoop
import SteppedFlapjack.LoopLiveSteps.TailEntryShape
import SteppedFlapjack.LoopLiveSteps.TailEntryGlobalBound
import SteppedFlapjack.LoopToWordSteps.TailCall

/-! Quantitative compilation of declarations with terminal bodies. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- A direct declaration initializer enters the body under a fresh Loop local.
For a terminal body, no local restoration is needed at the observable result. -/
theorem directDecl_terminal_bound {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (e : CrepExpHOL width) (shape : DirectExpression e) (body : CrepProgHOL width)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (factor : Nat)
    (continuation : @ProgramBound width _ σ body
      {ctxt with vars := ctxt.vars.updateEq (name,ctxt.vmax+1), vmax := ctxt.vmax+1}
      (sptInsert (ctxt.vmax+1) () live) factor)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ)
    (run : evalCrepSemHOLProgExact source (.dec name e body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ extra targetFinal,
      evaluate (compileHOLExact ctxt live (.dec name e body)) {target with clock := target.clock+extra} =
        (resultToLoop result,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      LoopSteps.steps (compileHOLExact ctxt live (.dec name e body)) {target with clock := target.clock+extra} ≤
        (factor+4) * (CrepSteps.steps (.dec name e body) source+1) := by
  classical
  rw [evalCrepSemHOLProgExact_dec_holShape] at run
  cases hev : evalCrepSemHOLExp source e with
  | none =>
    simp only [hev, Prod.mk.injEq] at run
    exact absurd run.1.symm nonerror
  | some v =>
    simp only [hev] at run
    let sourceBody := CrepSemHOLState.setVar name v source
    let tmp := ctxt.vmax+1
    let bodyCtxt := {ctxt with vars := ctxt.vars.updateEq (name,tmp), vmax := tmp}
    let bodyLive := sptInsert tmp () live
    let targetBody := LoopSemStateFiniteExact.setVar tmp (wlabWlocExact v) target
    rcases bodyRun : evalCrepSemHOLProgExact sourceBody body with ⟨bodyResult,bodyFinal⟩
    change evalCrepSemHOLProgExact {source with locals := source.locals.updateEq (name,v)} body = _ at bodyRun
    rw [bodyRun] at run
    simp only [Prod.mk.injEq] at run
    obtain ⟨hResult,hFinal⟩ := run
    obtain ⟨value,compiled,hValue⟩ := directExpression_preserves_eval e shape source v target ctxt tmp live
      hev stateRel memRel globalsRel codeRel localsRel (by simp [tmp])
    have entered := crepToLoopNcompileDecLocalsEnter ctxt live source.locals target.locals name tmp v localsRel (by simp [tmp])
    have bodyLocals : crepToLoopLocalsRelExact bodyCtxt bodyLive sourceBody.locals targetBody.locals := by
      simpa [sourceBody,targetBody,bodyLive,bodyCtxt,CrepSemHOLState.setVar,
        LoopSemStateFiniteExact.setVar,wlabWlocExact,wlabWlocHOL] using entered
    have bodyState : crepToLoopStateRelExact sourceBody targetBody := by
      simpa [sourceBody,CrepSemHOLState.setVar,targetBody,crepToLoopStateRelExact,LoopSemStateFiniteExact.setVar] using stateRel
    have bodyMem : crepToLoopMemRelHOLExact sourceBody.memory targetBody.memory sourceBody.memaddrs := by
      simpa [sourceBody,CrepSemHOLState.setVar,targetBody,LoopSemStateFiniteExact.setVar] using memRel
    have bodyGlobals : crepToLoopGlobalsRelHOLExact sourceBody.globals targetBody.globals := by
      simpa [sourceBody,CrepSemHOLState.setVar,targetBody,LoopSemStateFiniteExact.setVar] using globalsRel
    have bodyCode : crepToLoopCodeRelExact bodyCtxt sourceBody.code targetBody.code := by
      simpa [sourceBody,CrepSemHOLState.setVar,targetBody,bodyCtxt,crepToLoopCodeRelExact,LoopSemStateFiniteExact.setVar] using codeRel
    have bodyNonerror : bodyResult ≠ some .error := by simpa [hResult] using nonerror
    obtain ⟨extra,targetFinal,bodyEval,postState,postMem,postGlobals,postCode,_,bound⟩ :=
      continuation sourceBody bodyFinal bodyResult targetBody bodyRun bodyNonerror bodyState bodyMem bodyGlobals bodyCode bodyLocals
    have assignEval : evaluate (.assign tmp value) {target with clock := target.clock+extra} =
        (none,{targetBody with clock := targetBody.clock+extra}) := by
      rw [evaluate.eq_3]
      simp [eval_upd_clock_eq,hValue,targetBody,LoopSemStateFiniteExact.setVar]
    have comp : compileHOLExact ctxt live (.dec name e body) =
        .seq (loopNestedSeqHOL []) (.seq (.assign tmp value) (compileHOLExact bodyCtxt bodyLive body)) := by
      dsimp [tmp] at compiled
      simp only [compileHOLExact,compiled]
      rfl
    have seqCount := LoopSteps.steps_seq (loopNestedSeqHOL [])
      (.seq (.assign tmp value) (compileHOLExact bodyCtxt bodyLive body)) {target with clock := target.clock+extra}
    have innerCount := LoopSteps.steps_seq (.assign tmp value) (compileHOLExact bodyCtxt bodyLive body)
      {target with clock := target.clock+extra}
    rw [assignEval] at innerCount
    refine ⟨extra,targetFinal,?_,?_,?_,?_,?_,?_⟩
    · rw [comp]
      simp only [loopNestedSeqHOL,evaluate_seq,evaluate,assignEval]
      simpa [hResult] using bodyEval
    · rw [← hFinal]; simpa [crepToLoopStateRelExact] using postState
    · rw [← hFinal]; simpa using postMem
    · rw [← hFinal]; simpa using postGlobals
    · rw [← hFinal]; simpa [crepToLoopCodeRelExact,bodyCtxt] using postCode
    · rw [comp,CrepSteps.steps_dec,hev]
      simp only
      simp [loopNestedSeqHOL,LoopSteps.steps_leaf,evaluate] at seqCount
      simp [LoopSteps.steps_leaf] at innerCount
      simp only [loopNestedSeqHOL]
      rw [seqCount,innerCount]
      nlinarith

/-- A declaration enclosing an initialized loop and continuation has a proved
Crep-to-Loop execution bound with a factor computed from compiled syntax. -/
theorem directDecl_branchWhileBranch_bound {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (e : CrepExpHOL width) (shape : DirectExpression e)
    (init : CrepProgHOL width) (condition : CrepExpHOL width) (body tail : CrepProgHOL width)
    (initShape : BranchProgram init) (conditionShape : DirectExpression condition)
    (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ)
    (run : evalCrepSemHOLProgExact source (.dec name e (.seq init (.seq (.while condition body) tail))) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let bodyCtxt := {ctxt with vars := ctxt.vars.updateEq (name,ctxt.vmax+1), vmax := ctxt.vmax+1}
    let bodyLive := sptInsert (ctxt.vmax+1) () live
    let factor := 1 + sizeOf (compileHOLExact bodyCtxt bodyLive init) +
      (1 + (1 + sizeOf (compileHOLExact bodyCtxt bodyLive (.while condition body))) *
        (sizeOf (compileHOLExact bodyCtxt bodyLive body)+3) + sizeOf (compileHOLExact bodyCtxt bodyLive tail))
    ∃ extra targetFinal,
      evaluate (compileHOLExact ctxt live (.dec name e (.seq init (.seq (.while condition body) tail))))
          {target with clock := target.clock+extra} = (resultToLoop result,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      LoopSteps.steps (compileHOLExact ctxt live (.dec name e (.seq init (.seq (.while condition body) tail))))
        {target with clock := target.clock+extra} ≤
        (factor+4) * (CrepSteps.steps (.dec name e (.seq init (.seq (.while condition body) tail))) source+1) := by
  exact directDecl_terminal_bound name e shape (.seq init (.seq (.while condition body) tail)) ctxt live _
    (branchWhileBranch_programBound init initShape condition conditionShape body tail bodyShape tailShape _ _)
    source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel

/-- Declaration compilation produces the supported Loop sequence, including
its fresh-local assignment. -/
theorem directDecl_branchWhileBranch_shape {width : Nat} [NeZero width]
    (name : Nat) (e : CrepExpHOL width) (shape : DirectExpression e)
    (init : CrepProgHOL width) (condition : CrepExpHOL width) (body tail : CrepProgHOL width)
    (initShape : BranchProgram init) (conditionShape : DirectExpression condition)
    (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSequenceSource (compileHOLExact ctxt live (.dec name e (.seq init (.seq (.while condition body) tail)))) := by
  obtain ⟨value,compiled⟩ := directExpression_noCode shape ctxt (ctxt.vmax+1) live
  rw [compileHOLExact,compiled]
  exact .seq (.branch .skip) (.seq (.branch (.assign _ _))
    (branchConditionWhileBranch_wordSimpShape init initShape condition (.direct conditionShape)
      body tail bodyShape tailShape _ _))

/-- The real Loop optimizer preserves the declaration-wrapped execution and
its visit count is bounded by the corresponding Crep execution. -/
theorem directDecl_branchWhileBranch_optimised_bound {F : Type}
    (name : Nat) (e : CrepExpHOL 64) (shape : DirectExpression e)
    (init : CrepProgHOL 64) (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (initShape : BranchProgram init) (conditionShape : DirectExpression condition)
    (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F)
    (run : evalCrepSemHOLProgExact source (.dec name e (.seq init (.seq (.while condition body) tail))) = (result,sourceFinal))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let p := .dec name e (.seq init (.seq (.while condition body) tail))
    let bodyCtxt := {ctxt with vars := ctxt.vars.updateEq (name,ctxt.vmax+1), vmax := ctxt.vmax+1}
    let bodyLive := sptInsert (ctxt.vmax+1) () live
    let factor := 1 + sizeOf (compileHOLExact bodyCtxt bodyLive init) +
      (1 + (1 + sizeOf (compileHOLExact bodyCtxt bodyLive (.while condition body))) *
        (sizeOf (compileHOLExact bodyCtxt bodyLive body)+3) + sizeOf (compileHOLExact bodyCtxt bodyLive tail))
    ∃ extra targetFinal,
      evaluate (ocompileHOLExact ctxt live p) {target with clock := target.clock+extra} =
        (resultToLoop result,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      LoopSteps.steps (ocompileHOLExact ctxt live p) {target with clock := target.clock+extra} ≤
        sizeOf (ocompileHOLExact ctxt live p) * (2 * ((factor+4) * (CrepSteps.steps p source+1)) + 1) := by
  obtain ⟨extra,final,loopRun,postRel,_,_,_,loopBound⟩ :=
    directDecl_branchWhileBranch_bound name e shape init condition body tail initShape conditionShape bodyShape tailShape
      ctxt live source sourceFinal result target run (completeCrep_nonerror complete) stateRel memRel globalsRel codeRel localsRel
  obtain ⟨optRun,_,optBound⟩ := LoopLiveSteps.optimise_complete_source_steps
    (directDecl_branchWhileBranch_shape name e shape init condition body tail initShape conditionShape bodyShape tailShape ctxt live)
    {target with clock := target.clock+extra} final (resultToLoop result) loopRun (completeCrep_loop complete)
  refine ⟨extra,final,?_,postRel,?_⟩
  · simpa [ocompileHOLExact] using optRun
  · unfold ocompileHOLExact
    exact optBound.trans (Nat.mul_le_mul_left _ (by omega))

/-- A zero-argument tail call reaches the optimized declaration-wrapped
callee with a bound obtained from its actual Crep execution. -/
theorem compile_tailCall_nil_decl_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (caller : CrepSemHOLState 64 F)
    (target : LoopSemStateFiniteExact 64 F) (callee : MlString)
    (name : Nat) (e : CrepExpHOL 64) (shape : DirectExpression e)
    (init : CrepProgHOL 64) (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (initShape : BranchProgram init) (conditionShape : DirectExpression condition)
    (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (codeRel : crepToLoopCodeRelExact ctxt caller.code target.code)
    (found : caller.code.lookup callee = some ([],.dec name e (.seq init (.seq (.while condition body) tail))))
    (clock : target.clock ≠ 0)
    (run : evalCrepSemHOLProgExact source (.dec name e (.seq init (.seq (.while condition body) tail))) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source {decClock target with locals := .ln})
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (calleeCodeRel : crepToLoopCodeRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) source.code target.code)
    (localsRel : crepToLoopLocalsRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln source.locals .ln) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := .dec name e (.seq init (.seq (.while condition body) tail))
    let bc := {c with vars := c.vars.updateEq (name,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let factor := 1 + sizeOf (compileHOLExact bc bl init) +
      (1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
        (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail))
    ∃ extra final,
      evaluate (compileHOLExact ctxt live (.call none callee [])) {target with clock := target.clock+extra} =
        (resultToLoop result,final) ∧ crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call none callee [])) {target with clock := target.clock+extra} ≤
        3 + sizeOf (ocompileHOLExact c .ln p) * (2 * ((factor+4) * (CrepSteps.steps p source+1)) + 1) := by
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p : CrepProgHOL 64 := .dec name e (.seq init (.seq (.while condition body) tail))
  let entry : LoopSemStateFiniteExact 64 F := {decClock target with locals := .ln}
  obtain ⟨extra,final,optRun,postRel,optBound⟩ := directDecl_branchWhileBranch_optimised_bound
    name e shape init condition body tail initShape conditionShape bodyShape tailShape c .ln source post result entry
    run complete stateRel memRel globalsRel calleeCodeRel localsRel
  have shift : ({decClock {target with clock := target.clock+extra} with locals := .ln} : LoopSemStateFiniteExact 64 F) =
      {entry with clock := entry.clock+extra} := by
    simp only [entry,decClock]
    congr 1
    omega
  have extendedRun : evaluate (ocompileHOLExact c .ln p)
      {decClock {target with clock := target.clock+extra} with locals := .ln} = (resultToLoop result,final) := by
    rw [shift]; exact optRun
  have codeRel' : crepToLoopCodeRelExact ctxt caller.code {target with clock := target.clock+extra}.code := codeRel
  have lookup := tailCall_nil_lookup ctxt caller {target with clock := target.clock+extra} callee p codeRel' found
  have compiledRun : evaluate (compileHOLExact ctxt live (.call none callee [])) {target with clock := target.clock+extra} =
      (resultToLoop result,final) := by
    rw [compile_tailCall_nil,evaluate_seq]
    have callRun : evaluate (.call none (some (findLabExact ctxt callee)) [] none) {target with clock := target.clock+extra} =
        (resultToLoop result,final) := by
      rw [evaluate]
      simp only [show getVars [] {target with clock := target.clock+extra} = some [] from rfl,
        lookup,Option.isSome_none,Bool.false_eq_true,if_false]
      have nz : target.clock + extra ≠ 0 := by omega
      simp only [nz, dite_false]
      rw [extendedRun]
      cases complete <;> rfl
    rw [callRun]
    cases complete <;> rfl
  refine ⟨extra,final,compiledRun,postRel,?_⟩
  have count := compile_tailCall_nil_steps ctxt live caller {target with clock := target.clock+extra} callee p
    codeRel' found (by simp; omega)
  rw [shift] at count
  dsimp only [c,p] at count optBound ⊢
  exact count.trans (by omega)

/-- A successful initializer followed by a declaration-wrapped callee has a
Loop execution bounded by the visits of the entire Crep entry. -/
theorem branch_tailCall_nil_decl_entry_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (callee : MlString)
    (entryInit : CrepProgHOL 64) (entryShape : BranchProgram entryInit)
    (name : Nat) (e : CrepExpHOL 64) (shape : DirectExpression e)
    (init : CrepProgHOL 64) (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (initShape : BranchProgram init) (conditionShape : DirectExpression condition)
    (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F)
    (initRun : evalCrepSemHOLProgExact source entryInit = (none,middle))
    (found : middle.code.lookup callee = some ([],.dec name e (.seq init (.seq (.while condition body) tail))))
    (clock : middle.clock ≠ 0)
    (run : evalCrepSemHOLProgExact (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []})
      (.dec name e (.seq init (.seq (.while condition body) tail))) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := .dec name e (.seq init (.seq (.while condition body) tail))
    let bc := {c with vars := c.vars.updateEq (name,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let factor := 1 + sizeOf (compileHOLExact bc bl init) +
      (1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
        (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail))
    ∃ extra final,
      evaluate (compileHOLExact ctxt live (.seq entryInit (.call none callee [])))
        {target with clock := target.clock+extra} = (resultToLoop result,final) ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.seq entryInit (.call none callee [])))
        {target with clock := target.clock+extra} ≤
      4 + sizeOf (compileHOLExact ctxt live entryInit) + sizeOf (ocompileHOLExact c .ln p) *
        (2 * ((factor+4) * (CrepSteps.steps (.seq entryInit (.call none callee [])) source+1)) + 1) := by
  obtain ⟨firstExtra,firstResult,firstTarget,firstRun,firstState,firstMem,firstGlobals,
    firstCode,firstMap,firstLocals,_,_⟩ :=
    branchProgram_correct_with_bounded_extra entryInit entryShape source middle none target ctxt live
      initRun (by simp) stateRel memRel globalsRel codeRel localsRel
  have firstNone : firstResult = none := by simpa [resultToLoop] using firstMap
  subst firstResult
  have targetClock : firstTarget.clock ≠ 0 := by
    have h := firstState.2.2.1
    omega
  have ⟨calleeState,calleeMem,calleeGlobals,calleeCode,calleeLocals⟩ :=
    tailCall_nil_entry_relations ctxt live middle firstTarget callee _ firstState firstMem firstGlobals firstCode firstLocals found
  obtain ⟨callExtra,final,callRun,finalRel,callBound⟩ :=
    compile_tailCall_nil_decl_bound ctxt live middle firstTarget callee name e shape init condition body tail
      initShape conditionShape bodyShape tailShape _ post result firstCode found targetClock run complete
      calleeState calleeMem calleeGlobals calleeCode calleeLocals
  have lifted := evaluate_add_clock_eq (compileHOLExact ctxt live entryInit)
    {target with clock := target.clock+firstExtra} none firstTarget callExtra firstRun (by simp)
  have firstLift : evaluate (compileHOLExact ctxt live entryInit) {target with clock := target.clock+(firstExtra+callExtra)} =
      (none,{firstTarget with clock := firstTarget.clock+callExtra}) := by
    simpa [Nat.add_assoc] using lifted
  have firstBound := LoopSteps.branchedProgram_static_bound (compile_branchProgram entryShape ctxt live)
    {target with clock := target.clock+(firstExtra+callExtra)}
  have count := LoopSteps.steps_seq (compileHOLExact ctxt live entryInit) (compileHOLExact ctxt live (.call none callee []))
    {target with clock := target.clock+(firstExtra+callExtra)}
  rw [firstLift] at count
  have countLe := tailEntry_callee_steps_le entryInit callee (.dec name e (.seq init (.seq (.while condition body) tail)))
    source middle initRun found clock
  refine ⟨firstExtra+callExtra,final,?_,finalRel,?_⟩
  · rw [compileHOLExact,evaluate_seq,firstLift]
    exact callRun
  · rw [compileHOLExact]
    simp only at count
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let bc := {c with vars := c.vars.updateEq (name,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let factor := 1 + sizeOf (compileHOLExact bc bl init) +
      (1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
        (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail))
    have scaled := Nat.mul_le_mul_left (sizeOf (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
      (.dec name e (.seq init (.seq (.while condition body) tail)))))
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (factor+4) (Nat.add_le_add_right countLe 1))) 1)
    dsimp only [c,bc,bl,factor] at scaled
    omega

/-- The optimized entry has the actual tail-entry shape and a visit bound
in terms of the full Crep entry execution. -/
theorem branch_tailCall_nil_decl_optimised_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (callee : MlString)
    (entryInit : CrepProgHOL 64) (entryShape : BranchProgram entryInit)
    (name : Nat) (e : CrepExpHOL 64) (shape : DirectExpression e)
    (init : CrepProgHOL 64) (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (initShape : BranchProgram init) (conditionShape : DirectExpression condition)
    (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F) (wordCtxt : Spt Nat) (labels : Nat × Nat)
    (initRun : evalCrepSemHOLProgExact source entryInit = (none,middle))
    (found : middle.code.lookup callee = some ([],.dec name e (.seq init (.seq (.while condition body) tail))))
    (clock : middle.clock ≠ 0)
    (run : evalCrepSemHOLProgExact (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []})
      (.dec name e (.seq init (.seq (.while condition body) tail))) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := .dec name e (.seq init (.seq (.while condition body) tail))
    let bc := {c with vars := c.vars.updateEq (name,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let factor := 1 + sizeOf (compileHOLExact bc bl init) +
      (1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
        (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail))
    let entry := compileHOLExact ctxt live (.seq entryInit (.call none callee []))
    let limit := 4 + sizeOf (compileHOLExact ctxt live entryInit) + sizeOf (ocompileHOLExact c .ln p) *
      (2 * ((factor+4) * (CrepSteps.steps (.seq entryInit (.call none callee [])) source+1)) + 1)
    ∃ extra final,
      evaluate (optimiseHOL entry) {target with clock := target.clock+extra} = (resultToLoop result,final) ∧
      LoopLiveSteps.WordTailEntryShape (LoopToWord.compHOL wordCtxt (optimiseHOL entry) labels).1 ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (optimiseHOL entry) {target with clock := target.clock+extra} ≤
        (sizeOf (optimiseHOL entry) + sizeOf (ocompileHOLExact c .ln p)) * (2 * limit + 1) := by
  obtain ⟨extra,final,loopRun,rel,bound⟩ := branch_tailCall_nil_decl_entry_bound ctxt live callee entryInit entryShape
    name e shape init condition body tail initShape conditionShape bodyShape tailShape source middle post result target
    initRun found clock run complete stateRel memRel globalsRel codeRel localsRel
  have entryLoopShape := LoopLiveSteps.compiled_singleTail_shape ctxt live entryInit entryShape callee
  have codeEq := evaluateCodeInvariantHOL entryInit source none middle initRun
  have foundSource : source.code.lookup callee = some ([],.dec name e (.seq init (.seq (.while condition body) tail))) := by
    simpa only [codeEq] using found
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 callee [] _ foundSource
  have lenZero : len = 0 := by simpa using hlen.symm
  subst len
  have label : findLabExact ctxt callee = loc := by simp [findLabExact,hlab]
  have calleeShape := LoopLiveSteps.optimise_sequence
    (directDecl_branchWhileBranch_shape name e shape init condition body tail initShape conditionShape
      bodyShape tailShape (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln)
  have code : LoopLiveSteps.TailCodeBound {target with clock := target.clock+extra}.code
      (findLabExact ctxt callee)
      (sizeOf (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
        (.dec name e (.seq init (.seq (.while condition body) tail))))) := by
    intro calleeBody lookup
    rw [label] at lookup
    have eq : calleeBody = ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
        (.dec name e (.seq init (.seq (.while condition body) tail))) := by
      have h := Option.some.inj (lookup.symm.trans hcode)
      exact (Prod.mk.inj h).2
    subst calleeBody
    exact ⟨by simpa only [ocompileHOLExact] using calleeShape, le_rfl⟩
  obtain ⟨optRun,optShape,optBound⟩ := LoopLiveSteps.optimise_tailEntry_source_bound entryLoopShape
    {target with clock := target.clock+extra} final (resultToLoop result) _ code loopRun (completeCrep_loop complete)
  have wordShape := LoopLiveSteps.tailEntry_word (LoopLiveSteps.singleTail_to_tail optShape) wordCtxt labels
  refine ⟨extra,final,optRun,wordShape,rel,?_⟩
  exact optBound.trans (Nat.mul_le_mul_left _ (by omega))

end SteppedFlapjack.CrepToLoopSteps
