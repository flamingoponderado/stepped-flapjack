import SteppedFlapjack.CrepToLoopSteps.Branch
import SteppedFlapjack.LoopSteps.IterationClock
import SteppedFlapjack.CrepSteps.WhileClock

/-! Clock-consumption bound for the actual compiled Crep while loop. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps
open Flapjack.Compiler.Encoders.Asm

/-- The loop body generated for a direct Crep condition. -/
def directWhileBody {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (condition : HolLoopExp width)
    (body : CrepProgHOL width) : HolLoopProg width :=
  loopNestedSeqHOL [.assign (ctxt.vmax + 1) condition,
    .ite .notEqual (ctxt.vmax + 1) (.imm (0 : BitVec width))
      (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live]

/-- The actual Crep compiler emits a Loop loop with a loop-free body, for a
loop-free Crep body and direct condition. -/
theorem compile_directWhile {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (hcond : DirectExpression condition)
    (body : CrepProgHOL width) (hbody : BranchProgram body)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    ∃ conditionCode,
      compileHOLExact ctxt live (.while condition body) =
        .loop live (directWhileBody ctxt live conditionCode body) live ∧
      BranchedProgram (directWhileBody ctxt live conditionCode body) ∧
      LoopSelectProgram (compileHOLExact ctxt live (.while condition body)) := by
  obtain ⟨conditionCode,h⟩ := directExpression_noCode hcond ctxt (ctxt.vmax + 1) live
  refine ⟨conditionCode,?_,?_,?_⟩
  · simp only [compileHOLExact,h,List.nil_append,directWhileBody]
  · simp only [directWhileBody,loopNestedSeqHOL]
    exact .seq (.leaf (.assign _ _))
      (.seq (.ite _ _ _ _ (.seq (compile_branchProgram hbody ctxt live) (.leaf (.continue 0)))
        (.leaf (.break 0))) (.leaf .skip))
  · simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    exact .loop _ _ (.seq (.assign _ _) (.seq
      (.ite _ _ _ _ (.seq (compile_branchProgram_select hbody ctxt live) (.leaf (.continue 0)))
        (.leaf (.break 0))) (.leaf .skip)))

/-- Semantic correctness and a Loop-step bound by source visits and the extra
compiler clock. Bounding that extra clock by source visits remains open. -/
theorem directWhile_correct_by_clock {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (hcond : DirectExpression condition)
    (body : CrepProgHOL width) (hbody : BranchProgram body)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source (.while condition body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ conditionCode extra targetResult targetFinal,
      compileHOLExact ctxt live (.while condition body) = .loop live (directWhileBody ctxt live conditionCode body) live ∧
      evaluate (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock + extra} =
        (targetResult,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧ localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock + extra} ≤
        (1 + sizeOf (directWhileBody ctxt live conditionCode body)) *
          (CrepSteps.steps (.while condition body) source + extra + 1) := by
  obtain ⟨conditionCode,compiled,bodyShape,_⟩ := compile_directWhile condition hcond body hbody ctxt live
  obtain ⟨extra,targetResult,targetFinal,targetRun,finalState,finalMem,finalGlobals,finalCode,resultMap,finalLocals⟩ :=
    crepToLoopNcompileCorrectOf (.while condition body) source result sourceFinal target ctxt live
      run nonerror stateRel memRel globalsRel codeRel localsRel
  refine ⟨conditionCode,extra,targetResult,targetFinal,compiled,targetRun,finalState,finalMem,finalGlobals,
    finalCode,resultMap,finalLocals,?_⟩
  have targetLoop : evaluate (.loop live (directWhileBody ctxt live conditionCode body) live)
      {target with clock := target.clock + extra} = (targetResult,targetFinal) := by
    simpa only [compiled] using targetRun
  have count := LoopSteps.loop_steps_by_clock_consumption live live (directWhileBody ctxt live conditionCode body)
    bodyShape {target with clock := target.clock + extra} targetFinal targetResult targetLoop
  have sourceCount := CrepSteps.while_clock_consumed condition body hbody source sourceFinal result run
  have budget : source.clock + extra - sourceFinal.clock + 1 ≤
      CrepSteps.steps (.while condition body) source + extra + 1 := by omega
  have scaled := Nat.mul_le_mul_left (1 + sizeOf (directWhileBody ctxt live conditionCode body)) budget
  rw [compiled]
  exact Nat.le_trans (by simpa only [stateRel.2.2.1,finalState.2.2.1] using count) scaled

end SteppedFlapjack.CrepToLoopSteps
