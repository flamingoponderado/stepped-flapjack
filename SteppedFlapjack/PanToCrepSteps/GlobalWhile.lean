import SteppedFlapjack.PanToCrepSteps.GlobalShapes
import SteppedFlapjack.PanToCrepSteps.BranchWhile
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock

/-! Control-visit bounds for the globals pass on supported loops. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A non-error source loop and its globals-lowered loop take corresponding
iterations. The cost factor is determined by the lowered body syntax. -/
theorem globalCompile_while_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (condition : ExpHOL width) (body : ProgHOL width) (shape : BranchProgram ctxt body)
    (source sourceFinal target : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (run : source.evaluateHOLFiniteState (.while condition body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true globals source target) :
    controlSteps (compileProgExactHOL globals (.while condition body)) target ≤
      (1 + sizeOf (compileProgExactHOL globals body)) * controlSteps (.while condition body) source := by
  classical
  induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal result target with
  | _ clock ih =>
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite] at run
    split at run
    case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
    rename_i w heval
    have ht := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source condition (.val (.word w)) globals target ⟨rel,heval⟩
    change @evalHOLFinite width σ _ target (fun a => Classical.propDecidable (target.memaddrs a))
      (compileExpExactHOL globals condition) = some (.val (.word w)) at ht
    have hevalExact : @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) condition = some (.val (.word w)) := heval
    have htExact : @evalHOLExact width σ _ target.toExact
        (fun a => Classical.propDecidable (target.memaddrs a)) (compileExpExactHOL globals condition) = some (.val (.word w)) := ht
    conv_lhs => rw [compileProgExactHOL]
    rw [controlSteps_while]
    simp only [htExact]
    have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
    by_cases nz : w ≠ 0
    · by_cases z : source.clock = 0
      · have tz : target.clock = 0 := clockRel ▸ z
        simp only [tz,ne_eq,not_true_eq_false,and_false,if_false,Nat.add_zero]
        have positive := controlSteps_pos (.while condition body) source
        nlinarith
      · have tz : target.clock ≠ 0 := clockRel ▸ z
        simp only [if_pos (show w ≠ 0 ∧ target.clock ≠ 0 from ⟨nz,tz⟩)]
        rw [if_pos nz,if_neg z] at run
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState body with ⟨bodyResult,sourcePost⟩
        rw [bodyRun] at run
        dsimp only at run
        have bodyNonerror : bodyResult ≠ some .error := by
          rintro rfl
          exact absurd (Prod.mk.inj run).1.symm nonerror
        have bodyRel := PanGlobalsStateRelationClock.stateRelDecClockHOL globals source target true rel
        obtain ⟨targetPost,targetRun,postRel⟩ :=
          PanGlobalsCompileCorrectAssembly.compileCorrectHOL body source.decClockHOLFinite bodyResult globals
            target.decClockHOLFinite sourcePost ⟨bodyRel,bodyRun,bodyNonerror⟩
        rw [targetRun]
        have bodyBound := branch_control_static (globalCompile_branch_shape globals shape) target.decClockHOLFinite
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite body
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [PanSemStateFiniteExact.decClockHOLFinite] at bodyClock
          omega
        have sourceCount := controlSteps_while condition body source
        simp only [hevalExact,if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        cases bodyResult with
        | none =>
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result run nonerror postRel rfl
          simp only [compileProgExactHOL] at recurse
          simp only at sourceCount ⊢
          nlinarith
        | some r =>
          cases r with
          | «continue» =>
            have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result run nonerror postRel rfl
            simp only [compileProgExactHOL] at recurse
            simp only at sourceCount ⊢
            nlinarith
          | error => exact absurd rfl bodyNonerror
          | «break» | timeOut | returned _ | finalFfi _ | exception _ _ =>
            simp only [Nat.add_zero]
            have positive := controlSteps_pos (.while condition body) source
            nlinarith
    · have tz : ¬ (w ≠ 0 ∧ target.clock ≠ 0) := fun h => nz h.1
      simp only [if_neg tz,Nat.add_zero]
      have positive := controlSteps_pos (.while condition body) source
      nlinarith


/-- A loop and its continuation are bounded together, including early exits. -/
theorem globalCompile_whileThenBranch_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (condition : ExpHOL width) (body tail : ProgHOL width)
    (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail)
    (source sourceFinal target : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (run : source.evaluateHOLFiniteState (.seq (.while condition body) tail) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true globals source target) :
    controlSteps (compileProgExactHOL globals (.seq (.while condition body) tail)) target ≤
      (2 + sizeOf (compileProgExactHOL globals body) + sizeOf (compileProgExactHOL globals tail)) *
        controlSteps (.seq (.while condition body) tail) source := by
  have seqRun := run
  rw [evaluateHOLFiniteState_seq_line780] at seqRun
  rcases firstRun : source.evaluateHOLFiniteState (.while condition body) with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  dsimp only at seqRun
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    exact nonerror (Prod.mk.inj seqRun).1.symm
  have bound := globalCompile_while_steps globals ctxt condition body bodyShape source middle target firstResult
    firstRun firstNonerror rel
  obtain ⟨targetPost,targetRun,_⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.while condition body) source firstResult globals target middle ⟨rel,firstRun,firstNonerror⟩
  have sourceCount := controlSteps_seq (.while condition body) tail source
  rw [firstRun] at sourceCount
  rw [compileProgExactHOL,controlSteps_seq,targetRun]
  cases firstResult with
  | none =>
    simp only
    have tailBound := branch_control_static (globalCompile_branch_shape globals tailShape) targetPost
    simp only at sourceCount
    nlinarith
  | some r =>
    simp only
    simp only at sourceCount
    nlinarith

/-- Initialization, loop, and continuation together have a control-visit
bound depending only on their lowered syntax. -/
theorem globalCompile_initializedLoop_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (init : ProgHOL width) (condition : ExpHOL width) (body tail : ProgHOL width)
    (initShape : BranchProgram ctxt init) (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail)
    (source sourceFinal target : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (run : source.evaluateHOLFiniteState (.seq init (.seq (.while condition body) tail)) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true globals source target) :
    controlSteps (compileProgExactHOL globals (.seq init (.seq (.while condition body) tail))) target ≤
      (3 + sizeOf (compileProgExactHOL globals init) + sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals tail)) *
        controlSteps (.seq init (.seq (.while condition body) tail)) source := by
  have seqRun := run
  rw [evaluateHOLFiniteState_seq_line780] at seqRun
  rcases firstRun : source.evaluateHOLFiniteState init with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  dsimp only at seqRun
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    exact nonerror (Prod.mk.inj seqRun).1.symm
  obtain ⟨targetPost,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    init source firstResult globals target middle ⟨rel,firstRun,firstNonerror⟩
  have initBound := branch_control_static (globalCompile_branch_shape globals initShape) target
  have sourceCount := controlSteps_seq init (.seq (.while condition body) tail) source
  rw [firstRun] at sourceCount
  rw [compileProgExactHOL,controlSteps_seq,targetRun]
  cases firstResult with
  | none =>
    have bound := globalCompile_whileThenBranch_steps globals ctxt condition body tail bodyShape tailShape
      middle sourceFinal targetPost result seqRun nonerror postRel
    simp only
    simp only at sourceCount
    nlinarith
  | some r =>
    simp only
    simp only at sourceCount
    nlinarith


/-- Composing global lowering with Pancake-to-Crep compilation bounds the
actual Crep visits in terms of the original initialized loop's visits. -/
theorem globalCompile_initializedLoop_crep_steps {width : Nat} [NeZero width] {σ : Type}
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (init : ProgHOL width) (condition : ExpHOL width) (body tail : ProgHOL width)
    (initShape : BranchProgram ctxt init) (conditionShape : ScalarExpression ctxt condition)
    (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail)
    (source sourceFinal lowered : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (crep : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.seq init (.seq (.while condition body) tail)) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (globalRel : panGlobalsStateRelHOLExact true globals source lowered)
    (stateRel : panToCrepStateRelFiniteExact lowered crep)
    (codeRel : codeRelExactHOLW ctxt lowered.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids lowered.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt lowered.locals crep.locals)
    (localised : localisedProgHOL (compileProgExactHOL globals (.seq init (.seq (.while condition body) tail))) = true) :
    CrepSteps.steps (compileProgExactHOLW ctxt (compileProgExactHOL globals (.seq init (.seq (.while condition body) tail)))) crep ≤
      ((3 + sizeOf (compileProgExactHOLW ctxt (compileProgExactHOL globals init)) +
          sizeOf (compileProgExactHOLW ctxt (compileProgExactHOL globals body)) +
          sizeOf (compileProgExactHOLW ctxt (compileProgExactHOL globals tail))) *
        (3 + sizeOf (compileProgExactHOL globals init) + sizeOf (compileProgExactHOL globals body) +
          sizeOf (compileProgExactHOL globals tail))) *
        controlSteps (.seq init (.seq (.while condition body) tail)) source := by
  obtain ⟨loweredFinal,loweredRun,_⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.seq init (.seq (.while condition body) tail)) source result globals lowered sourceFinal ⟨globalRel,run,nonerror⟩
  have sourceBound := globalCompile_initializedLoop_steps globals ctxt init condition body tail initShape bodyShape tailShape
    source sourceFinal lowered result run nonerror globalRel
  have crepBound := branchWhileBranch_compiled_steps
    (compileProgExactHOL globals init) (compileExpExactHOL globals condition)
    (compileProgExactHOL globals body) (compileProgExactHOL globals tail) ctxt
    (globalCompile_branch_shape globals initShape) (globalCompile_scalar_shape globals conditionShape)
    (globalCompile_branch_shape globals bodyShape) (globalCompile_branch_shape globals tailShape)
    lowered loweredFinal result crep (by simpa only [compileProgExactHOL] using loweredRun)
    nonerror stateRel codeRel excpRel localsRel (by simpa only [compileProgExactHOL] using localised)
  simp only [compileProgExactHOL] at sourceBound
  simpa only [compileProgExactHOL, Nat.mul_assoc] using crepBound.trans (Nat.mul_le_mul_left _ sourceBound)

end SteppedFlapjack.PanToCrepSteps
