import SteppedFlapjack.CrepToLoopSteps.WhileSequence

/-! Compositional bounds for a loop-free prefix. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- Semantic and quantitative correctness for one fixed compiled program. -/
def ProgramBound {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet) (factor : Nat) : Prop :=
  ∀ (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ),
    evalCrepSemHOLProgExact source p = (result,sourceFinal) → result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact ctxt source.code target.code →
    crepToLoopLocalsRelExact ctxt live source.locals target.locals →
    ∃ extra targetFinal,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+extra} = (resultToLoop result,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock+extra} ≤
        factor * (CrepSteps.steps p source+1)

/-- Prepending a supported branch preserves a continuation's proved bound.
This is a compositional lemma; its continuation premise is discharged by
specific program proofs. -/
theorem branchPrefix_bound {width : Nat} [NeZero width] {σ : Type}
    (headProg suffix : CrepProgHOL width) (shape : BranchProgram headProg)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (factor : Nat)
    (continuation : @ProgramBound width _ σ suffix ctxt live factor) :
    @ProgramBound width _ σ (.seq headProg suffix) ctxt live
      (1 + sizeOf (compileHOLExact ctxt live headProg) + factor) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  have seqRun := run
  rw [evalCrepSemHOLProgExact_seq_holShape] at seqRun
  rcases firstRun : evalCrepSemHOLProgExact source headProg with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  have sourceCount := CrepSteps.steps_seq headProg suffix source
  rw [firstRun] at sourceCount
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    simp only [Option.some_ne_none,if_false,Prod.mk.injEq] at seqRun
    exact nonerror seqRun.1.symm
  obtain ⟨firstExtra,firstTargetResult,firstTarget,firstTargetRun,firstState,firstMem,firstGlobals,
    firstCode,firstMap,firstLocals,_,_⟩ :=
    branchProgram_correct_with_bounded_extra headProg shape source middle firstResult target ctxt live
      firstRun firstNonerror stateRel memRel globalsRel codeRel localsRel
  cases firstResult with
  | none =>
    have firstNone : firstTargetResult = none := by simpa [resultToLoop] using firstMap
    subst firstTargetResult
    simp only at seqRun
    obtain ⟨secondExtra,final,secondRun,secondState,secondMem,secondGlobals,secondCode,secondLocals,secondBound⟩ :=
      continuation middle sourceFinal result firstTarget seqRun nonerror firstState firstMem firstGlobals firstCode firstLocals
    have lift := evaluate_add_clock_eq (compileHOLExact ctxt live headProg)
      {target with clock := target.clock+firstExtra} none firstTarget secondExtra firstTargetRun (by simp)
    have firstLift : evaluate (compileHOLExact ctxt live headProg)
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          (none,{firstTarget with clock := firstTarget.clock+secondExtra}) := by
      simpa [Nat.add_assoc] using lift
    have firstBound := LoopSteps.branchedProgram_static_bound (compile_branchProgram shape ctxt live)
      {target with clock := target.clock+(firstExtra+secondExtra)}
    have count := LoopSteps.steps_seq (compileHOLExact ctxt live headProg) (compileHOLExact ctxt live suffix)
      {target with clock := target.clock+(firstExtra+secondExtra)}
    rw [firstLift] at count
    refine ⟨firstExtra+secondExtra,final,?_,secondState,secondMem,secondGlobals,secondCode,secondLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstLift]
      exact secondRun
    · simp only at sourceCount count
      rw [compileHOLExact]
      nlinarith
  | some r =>
    simp only [Option.some_ne_none,if_false,Prod.mk.injEq] at seqRun
    obtain ⟨rfl,rfl⟩ := seqRun
    have targetSome : firstTargetResult ≠ none := by
      rw [firstMap]
      cases r <;> simp [resultToLoop]
    refine ⟨firstExtra,firstTarget,?_,firstState,firstMem,firstGlobals,firstCode,firstLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstTargetRun]
      cases firstTargetResult with
      | none => exact (targetSome rfl).elim
      | some v => simp [firstMap]
    · have count := LoopSteps.steps_seq (compileHOLExact ctxt live headProg) (compileHOLExact ctxt live suffix)
        {target with clock := target.clock+firstExtra}
      have bound := LoopSteps.branchedProgram_static_bound (compile_branchProgram shape ctxt live)
        {target with clock := target.clock+firstExtra}
      rw [firstTargetRun] at count
      cases firstTargetResult with
      | none => exact (targetSome rfl).elim
      | some v =>
        simp only at count sourceCount
        rw [compileHOLExact]
        have positive := CrepSteps.steps_pos (.seq headProg suffix) source
        nlinarith


/-- The while-and-continuation bound has a factor computed from compiled syntax,
without an existential expression in the factor. -/
theorem whileThenBranch_programBound {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (conditionShape : DirectExpression condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ (.seq (.while condition body) tail) ctxt live
      (1 + (1 + sizeOf (compileHOLExact ctxt live (.while condition body))) *
        (sizeOf (compileHOLExact ctxt live body)+3) + sizeOf (compileHOLExact ctxt live tail)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨value,extra,post,compiled,he,hs,hm,hg,hc,hl,bound⟩ :=
    whileThenBranch_correct_with_steps condition conditionShape body tail bodyShape tailShape source sourceFinal result
      target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
  refine ⟨extra,post,he,hs,hm,hg,hc,hl,?_⟩
  have bodySize : sizeOf (directWhileBody ctxt live value body) ≤
      sizeOf (compileHOLExact ctxt live (.while condition body)) := by
    rw [compiled]
    simp_wf
    omega
  have cost := Nat.mul_le_mul_right (sizeOf (compileHOLExact ctxt live body)+3)
    (Nat.add_le_add_left bodySize 1)
  apply Nat.le_trans bound
  apply Nat.mul_le_mul_right
  omega

/-- Initialization, loop, and continuation compile with a fully discharged
source-step bound; no correctness hypothesis is required for a subprogram. -/
theorem branchWhileBranch_programBound {width : Nat} [NeZero width] {σ : Type}
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : DirectExpression condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ (.seq init (.seq (.while condition body) tail)) ctxt live
      (1 + sizeOf (compileHOLExact ctxt live init) +
        (1 + (1 + sizeOf (compileHOLExact ctxt live (.while condition body))) *
          (sizeOf (compileHOLExact ctxt live body)+3) + sizeOf (compileHOLExact ctxt live tail))) :=
  branchPrefix_bound init (.seq (.while condition body) tail) initShape ctxt live _
    (whileThenBranch_programBound condition conditionShape body tail bodyShape tailShape ctxt live)

/-- The same compiled sequence lies in the selected RISC-V fragment. -/
theorem branchWhileBranch_select {width : Nat} [NeZero width]
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width) (conditionShape : DirectExpression condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSelectProgram (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) := by
  simpa only [compileHOLExact] using LoopSelectProgram.seq (compile_branchProgram_select initShape ctxt live)
    (whileThenBranch_select condition conditionShape body tail bodyShape tailShape ctxt live)

end SteppedFlapjack.CrepToLoopSteps
