import SteppedFlapjack.CrepToLoopSteps.WhileIteration

/-! Bounded compiler clock for direct-condition Crep loops. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

private theorem loop_timeout {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (body : HolLoopProg width) (target : LoopSemStateFiniteExact width F)
    (clockZero : target.clock = 0) (subset : sptSubsetLive live target.locals) :
    evaluate (.loop live body live) target = (some .timeOut,{target with locals := .ln}) := by
  have cut : cutRes live (none,target) = (some .timeOut,{target with locals := .ln}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live target subset]
    simp [clockZero]
  rw [evaluate]
  split
  next x h => rw [cut] at h; simp at h
  next h => exact cut

/-- Direct-condition loops with branch bodies admit a compiler clock bounded by
source evaluator visits and compiled-body syntax. -/
theorem directWhile_bounded_clock {width : Nat} [NeZero width] {F : Type}
    (condition : CrepExpHOL width) (conditionShape : DirectExpression condition)
    (body : CrepProgHOL width) (bodyShape : BranchProgram body)
    (source sourceFinal : CrepSemHOLState width F) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source (.while condition body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ extra post,
      extra ≤ (sizeOf (compileHOLExact ctxt live body)+2) * (CrepSteps.steps (.while condition body) source+1) ∧
      evaluate (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+extra} =
        (resultToLoop result,post) ∧
      crepToLoopStateRelExact sourceFinal post ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧
      localsResultRel ctxt live result sourceFinal post := by
  induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal result target with
  | _ clock ih =>
    rw [evalCrepSemHOLProgExact_while_holShape] at run
    rcases guard : evalCrepSemHOLExp source condition with _ | ⟨w⟩
    · simp only [guard,Prod.mk.injEq] at run
      exact absurd run.1.symm nonerror
    · simp only [guard] at run
      by_cases nz : w.1 ≠ 0
      · simp only [if_pos nz] at run
        by_cases zero : source.clock = 0
        · simp only [zero,if_true,Prod.mk.injEq] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨value,compiled,_,_⟩ := compile_directWhile condition conditionShape body bodyShape ctxt live
          have tz : target.clock = 0 := stateRel.2.2.1 ▸ zero
          have h := loop_timeout live (directWhileBody ctxt live value body) target tz localsRel.2.2.1
          refine ⟨0,{target with locals := .ln},by omega,?_,?_,?_,?_,?_,?_⟩
          · simpa [compiled,resultToLoop] using h
          · simpa [crepToLoopStateRelExact,CrepSemHOLState.emptyLocals] using stateRel
          · simpa [CrepSemHOLState.emptyLocals] using memRel
          · simpa [CrepSemHOLState.emptyLocals] using globalsRel
          · simpa [CrepSemHOLState.emptyLocals] using codeRel
          · trivial
        · simp only [if_neg zero] at run
          rcases bodyRun : evalCrepSemHOLProgExact (decClockCrepSemHOL source) body with ⟨bodyResult,postSource⟩
          simp only [bodyRun] at run
          have bodyClock := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL source) body
          rw [bodyRun] at bodyClock
          have smaller : postSource.clock < clock := by simp only [decClockCrepSemHOL] at bodyClock; omega
          have count := CrepSteps.steps_while condition body source
          simp only [guard,if_pos (show w.1 ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,zero⟩),bodyRun] at count
          have continueCase (hcontinue : bodyResult = none ∨ bodyResult = some (.continue 0))
              (rest : evalCrepSemHOLProgExact postSource (.while condition body) = (result,sourceFinal)) :
              ∃ extra post,
                extra ≤ (sizeOf (compileHOLExact ctxt live body)+2) * (CrepSteps.steps (.while condition body) source+1) ∧
                evaluate (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+extra} =
                  (resultToLoop result,post) ∧
                crepToLoopStateRelExact sourceFinal post ∧
                crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
                crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
                crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧
                localsResultRel ctxt live result sourceFinal post := by
            obtain ⟨first,middle,hfirst,hs,hm,hg,hcode,hl,step⟩ :=
              directWhile_continue_run condition conditionShape body bodyShape source postSource bodyResult target ctxt live
                w.1 guard nz zero bodyRun hcontinue stateRel memRel globalsRel codeRel localsRel
            obtain ⟨tail,post,htail,he,hstate,hmem,hglobal,hcode',hlocal⟩ :=
              ih postSource.clock smaller postSource sourceFinal result middle rest nonerror hs hm hg hcode hl rfl
            have counts : CrepSteps.steps (.while condition body) postSource + 1 ≤ CrepSteps.steps (.while condition body) source := by
              rcases hcontinue with h | h <;> simp only [h] at count <;> rw [count] <;>
                simp [Nat.add_comm]
            refine ⟨first+tail,post,?_,?_,hstate,hmem,hglobal,hcode',hlocal⟩
            · nlinarith
            · exact (step tail).trans he
          cases bodyResult with
          | none => exact continueCase (Or.inl rfl) run
          | some r =>
            by_cases hcont : r = .continue 0
            · subst r
              exact continueCase (Or.inr rfl) run
            · by_cases hbreak : r = .break 0
              · subst r
                simp only [Prod.mk.injEq] at run
                obtain ⟨rfl,rfl⟩ := run
                obtain ⟨extra,post,hbound,hs,hm,hg,hcode,hl,he⟩ :=
                  directWhile_break_run condition conditionShape body bodyShape source postSource target ctxt live
                    w.1 guard nz zero bodyRun stateRel memRel globalsRel codeRel localsRel
                exact ⟨extra,post,by nlinarith,by simpa [resultToLoop] using he,hs,hm,hg,hcode,by simpa [localsResultRel] using hl⟩
              · have eq : (exitLoopCrepResult (some r),postSource) = (result,sourceFinal) := by
                  cases r with
                  | «continue» n => cases n with | zero => exact absurd rfl hcont | succ n => exact run
                  | «break» n => cases n with | zero => exact absurd rfl hbreak | succ n => exact run
                  | _ => exact run
                simp only [Prod.mk.injEq] at eq
                obtain ⟨rfl,rfl⟩ := eq
                have ne : r ≠ .error := by intro h; subst r; exact nonerror rfl
                obtain ⟨extra,post,hbound,hs,hm,hg,hcode,hl,he⟩ :=
                  directWhile_exit_run condition conditionShape body bodyShape source postSource r target ctxt live
                    w.1 guard nz zero bodyRun hcont hbreak ne stateRel memRel globalsRel codeRel localsRel
                exact ⟨extra,post,by nlinarith,he,hs,hm,hg,hcode,hl⟩
      · have eq : w.1 = 0 := by simpa using nz
        have guard0 : evalCrepSemHOLExp source condition = some (.word 0) := by
          cases w with
          | word v =>
            change v = 0 at eq
            subst v
            exact guard
        simp only [if_neg nz,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨post,he,hs,hm,hg,hcode,hl⟩ :=
          directWhile_false_run condition conditionShape body source target ctxt live guard0
            stateRel memRel globalsRel codeRel localsRel
        exact ⟨2,post,by nlinarith,by simpa [resultToLoop] using he,hs,hm,hg,hcode,by simpa [localsResultRel] using hl⟩


/-- The same correctness witness bounds actual compiled Loop visits by a
source-step expression with factors computed from the compiled loop body. -/
theorem directWhile_bounded_steps {width : Nat} [NeZero width] {F : Type}
    (condition : CrepExpHOL width) (conditionShape : DirectExpression condition)
    (body : CrepProgHOL width) (bodyShape : BranchProgram body)
    (source sourceFinal : CrepSemHOLState width F) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source (.while condition body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ value extra post,
      evaluate (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+extra} =
        (resultToLoop result,post) ∧
      crepToLoopStateRelExact sourceFinal post ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧
      localsResultRel ctxt live result sourceFinal post ∧
      LoopSteps.steps (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+extra} ≤
        (1 + sizeOf (directWhileBody ctxt live value body)) *
        ((sizeOf (compileHOLExact ctxt live body)+3) * (CrepSteps.steps (.while condition body) source+1)) := by
  obtain ⟨value,compiled,bodyLoop,_⟩ := compile_directWhile condition conditionShape body bodyShape ctxt live
  obtain ⟨extra,post,clockBound,targetRun,hs,hm,hg,hc,hl⟩ :=
    directWhile_bounded_clock condition conditionShape body bodyShape source sourceFinal result target ctxt live
      run nonerror stateRel memRel globalsRel codeRel localsRel
  refine ⟨value,extra,post,targetRun,hs,hm,hg,hc,hl,?_⟩
  have loopRun : evaluate (.loop live (directWhileBody ctxt live value body) live)
      {target with clock := target.clock+extra} = (resultToLoop result,post) := by
    simpa [compiled] using targetRun
  have count := LoopSteps.loop_steps_by_clock_consumption live live (directWhileBody ctxt live value body)
    bodyLoop {target with clock := target.clock+extra} post (resultToLoop result) loopRun
  have sourceCount := CrepSteps.while_clock_consumed condition body bodyShape source sourceFinal result run
  have delta : source.clock + extra - sourceFinal.clock + 1 ≤
      CrepSteps.steps (.while condition body) source + extra + 1 := by omega
  have budget : source.clock + extra - sourceFinal.clock + 1 ≤
      (sizeOf (compileHOLExact ctxt live body)+3) * (CrepSteps.steps (.while condition body) source+1) := by
    nlinarith
  rw [compiled]
  exact Nat.le_trans (by simpa only [stateRel.2.2.1,hs.2.2.1] using count)
    (Nat.mul_le_mul_left _ budget)

end SteppedFlapjack.CrepToLoopSteps
