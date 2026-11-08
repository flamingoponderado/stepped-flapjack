import SteppedFlapjack.CrepToLoopSteps.ConditionInduction

/-! Explicit compiler clock for a scalar condition and a loop-free body. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A completed loop runs with a clock calculated from its source visits and
compiled syntax. The post-state relation ignores the deliberately added clock. -/
theorem branchConditionWhile_explicit {width : Nat} [NeZero width] {F : Type}
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body : CrepProgHOL width) (bodyShape : LoopFreeCrep body)
    (source sourceFinal : CrepSemHOLState width F) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet) (limit : Nat)
    (run : evalCrepSemHOLProgExact source (.while condition body) = (result,sourceFinal))
    (sourceBound : CrepSteps.steps (.while condition body) source ≤ limit)
    (nonerror : result ≠ some .error) (nontimeout : resultToLoop result ≠ some .timeOut)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let p := CrepProgHOL.while condition body
    let budget := (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
      sizeOf (compileHOLExact ctxt live body)+2) * (limit+1)
    ∃ post,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+budget} =
        (resultToLoop result,post) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧
      localsResultRel ctxt live result sourceFinal post ∧
      LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock+budget} ≤
        (1 + sizeOf (compileHOLExact ctxt live p)) * (limit+budget+1) := by
  let p := CrepProgHOL.while condition body
  let budget := (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
      sizeOf (compileHOLExact ctxt live body)+2) * (limit+1)
  obtain ⟨extra,oldPost,extraBound,oldRun,hs,hm,hg,hc,hl⟩ :=
    branchConditionWhile_bounded_clock condition conditionShape body (sizeOf (compileHOLExact ctxt live body)) source sourceFinal result target ctxt live
      (loopFree_linearBodySimulation body bodyShape ctxt live) run nonerror stateRel memRel globalsRel codeRel localsRel
  have extraBudget : extra ≤ budget := extraBound.trans (Nat.mul_le_mul_left _ (by omega))
  let delta := budget-extra
  have shifted := evaluate_add_clock_eq _ _ _ _ delta oldRun nontimeout
  have eq : target.clock+extra+delta = target.clock+budget := by dsimp [delta]; omega
  have newRun : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+budget} =
      (resultToLoop result,{oldPost with clock := oldPost.clock+delta}) := by simpa [p,eq] using shifted
  obtain ⟨code,value,next,outLive,_,compiled,bodyLoop,_⟩ :=
    branchCondition_compileWhile condition conditionShape body bodyShape ctxt live
  have loopRun : evaluate (.loop live (branchConditionWhileBody ctxt live code value next body) live)
      {target with clock := target.clock+budget} = (resultToLoop result,{oldPost with clock := oldPost.clock+delta}) := by
    simpa [p,compiled] using newRun
  have count := LoopSteps.loop_steps_by_clock_consumption live live _ bodyLoop _ _ _ loopRun
  have consumed := CrepSteps.while_clock_consumed condition body bodyShape source sourceFinal result run
  have initial := stateRel.2.2.1
  have final := hs.2.2.1
  refine ⟨{oldPost with clock := oldPost.clock+delta},newRun,?_,?_,?_,?_,?_,?_⟩
  · simpa [crepToLoopStateRelExact,final] using hs
  · simpa using hm
  · simpa using hg
  · simpa using hc
  · cases result with
    | none => exact hl
    | some r => cases r <;> exact hl
  · rw [compiled]
    simp only at count consumed
    have factor : 1 + sizeOf (branchConditionWhileBody ctxt live code value next body) ≤
        1 + sizeOf (.loop live (branchConditionWhileBody ctxt live code value next body) live : HolLoopProg width) := by simp; omega
    have fuel : target.clock + budget - (oldPost.clock+delta) + 1 ≤
        limit + budget + 1 := by dsimp [p] at *; omega
    exact count.trans (Nat.le_trans (Nat.mul_le_mul_right _ factor) (Nat.mul_le_mul_left _ fuel))
end SteppedFlapjack.CrepToLoopSteps
