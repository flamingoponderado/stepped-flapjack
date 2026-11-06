import SteppedFlapjack.CrepToLoopSteps.BranchPrefix
import SteppedFlapjack.CrepToLoopSteps.DirectExpressionEval

/-! Quantitative compilation of declarations with terminal bodies. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

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

end SteppedFlapjack.CrepToLoopSteps
