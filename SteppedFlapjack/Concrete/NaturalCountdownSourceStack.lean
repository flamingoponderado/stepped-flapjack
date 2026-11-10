import SteppedFlapjack.Concrete.CountdownSourceStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
namespace SteppedFlapjack.Concrete

/-- Both source fixtures induce the same generated Crep state at a shared clock. -/
theorem countdownFixtures_crep_equal (n clock : Nat) :
  crepStateFrom (panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) clock)) (naturalCountdownHOL n) =
  crepStateFrom (panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) clock)) (naturalCountdownHOL n) := by
  simp [crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall,
    panSimpSourceState,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate]
/-- The unprefixed source compiles to the same Word table as the prefixed source. -/
theorem naturalCountdown_panToWord (n : Nat) :
 panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") (progToHOL (naturalCountdown n))) = countdownWordPrograms n := by
  have same : panSimpDeclsHOL (declarations (naturalCountdownHOL n)) = declarations (naturalCountdownHOL n) := by
    simp [declarations,singleEntryProgram,panSimpDeclsHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,
      retToTailHOL,seqCallRetHOL,naturalCountdownHOL,naturalCountdown,countdownBody,
      progToHOL,expToHOL,shapeToHOL]
  have h := countdown_panToWord n
  rw [← countdown_hol_eq n] at h
  change panToWordCompileProgHOL riscvConfig.isa (declarations (countdownHOL n)) = _ at h
  change panToWordCompileProgHOL riscvConfig.isa (declarations (naturalCountdownHOL n)) = _
  unfold panToWordCompileProgHOL at h ⊢
  rw [countdown_simp_declarations] at h
  rw [same]
  exact h

open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.WordToStackSteps Flapjack.WordToStackProofs.CompCorrect

/-- The unprefixed source uses the same Stack run and explicit bound at clock `6*n+9`. -/
theorem naturalCountdownFixture_source_stack (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit)
      (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config Unit) (targetResult : Option (StackSemResult 64)),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState (naturalCountdown n)
        (clockedFixtureSource (naturalCountdown n) (6*n+9))) (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧ targetPost.ffi = post.ffi ∧
      StackSemEvaluate.evaluate (.call none (.inl 64) none,
        {(countdownFixtureStack n cfg) with clock := countdownWordBound n+1}) = (targetResult,targetPost) ∧
      some (compileResult (.result (.loc 1 0) [.word 0])) = targetResult ∧
      SteppedFlapjack.StackSteps.steps (.call none (.inl 64) none,
        {(countdownFixtureStack n cfg) with clock := countdownWordBound n+1}) ≤
        9543650688*n+29426459323 := by
  have h := countdownFixture_source_stack n range cfg context primitive handler
  rw [countdownFixtures_crep_equal n (6*n+9)] at h
  exact h
end SteppedFlapjack.Concrete
