import SteppedFlapjack.Concrete.WitnessLoopCode
import SteppedFlapjack.Concrete.DeclarationEntry
import SteppedFlapjack.Concrete.CrepCountdown
import SteppedFlapjack.Concrete.CountedApplications
import SteppedFlapjack.CrepSteps.TailEntryReturn
import SteppedFlapjack.CrepToLoopSteps.DeclExplicit

/-! Link the phase-one countdown entry to its compiled optimized callee. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- The natural countdown has the same generated entry wrapper as the
comparison witness; only the callee code differs. -/
theorem naturalCountdown_loop_entry_code (arch : AsmArchitecture) (n : Nat) :
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) := by
  rw [naturalCountdown_loop_code]
  exact twoLoopPrograms_entry_code arch _ _ _ (Ne.symm (entryName_fresh (naturalCountdownHOL n)))

/-- The natural-countdown entry inherits an explicit bound from any returning
phase-one entry execution. -/
theorem naturalCountdown_entry_loop {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) (n limit : Nat)
    (nonzero : (crepStateFrom source (naturalCountdownHOL n)).clock ≠ 0)
    (entryRun : ∃ final, evalCrepSemHOLProgExact (crepStateFrom source (naturalCountdownHOL n))
      (naturalCrepEntry n) = (some (.return [.word 0]),final))
    (entryBound : CrepSteps.steps (naturalCrepEntry n) (crepStateFrom source (naturalCountdownHOL n)) ≤ limit) :
    let target := loopStateFrom arch source (naturalCountdownHOL n)
    let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := naturalCountdownCrepBody (BitVec.ofNat 64 n)
    let bc := {c with vars := c.vars.updateEq (1,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let body : CrepProgHOL 64 := .dec 2 (.op .sub [.var 1,.const 1]) (.seq (.assign 1 (.var 2)) .skip)
    let tail : CrepProgHOL 64 := .return [.const 0]
    let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while (.var 1) body))) *
      (sizeOf (compileHOLExact bc bl body)+4) + sizeOf (compileHOLExact bc bl tail)
    let bound := (factor+4)*(limit+1)
    let code := compileHOLExact c .ln p
    ∃ post,
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+2*bound} = (some (.result [.word 0]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1)+8 := by
  let crep := crepStateFrom source (naturalCountdownHOL n)
  let target := loopStateFrom arch source (naturalCountdownHOL n)
  let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
  let name := entryName (naturalCountdownHOL n)
  let body : CrepProgHOL 64 := .dec 2 (.op .sub [.var 1,.const 1]) (.seq (.assign 1 (.var 2)) .skip)
  let p := naturalCountdownCrepBody (BitVec.ofNat 64 n)
  have found : crep.code.lookup name = some ([],p) := by
    have h := generated_callee_lookup (naturalCountdownHOL n) p (natural_countdown_crep_code n)
    simpa [crep,name,crepState,crepStateFrom,PanToCrepSteps.concreteDeclCrepState] using h
  have label : findLabExact ctxt name = 65 := by
    have fresh := Ne.symm (entryName_fresh (naturalCountdownHOL n))
    have h := twoPrograms_callee_label arch (ofString "main") name p fresh
    simpa [ctxt,witnessLoopContext,natural_countdown_crep_code,twoPrograms,p] using h
  have rel := loopStateFrom_relations arch source (naturalCountdownHOL n)
  have codeLocals := naturalCountdown_loop_code_locals arch source n
  have bodyShape : BranchProgram body :=
    .dec (.op .sub (.var 1) (.const 1)) (.seq (.expr (.assign 1 (.var 2))) (.expr (.leaf .skip)))
  have scalar : ScalarProgram p := .dec 1 (.direct (.const _)) (.seq
    (.while (.direct (.var _)) (.dec 2 (.direct (.op .sub (.var 1) (.const 1)))
      (.seq (.assign 1 (.direct (.var 2))) .skip))) (.ret (.direct (.const 0))))
  have result := generatedDecl_entry_explicit ctxt name 1 (.const (BitVec.ofNat 64 n)) (.var 1) body (.return [.const 0])
    (.const _) (.var 1) bodyShape (.expr (.returnOne (.const 0))) scalar crep target [.word 0] limit
    nonzero found entryRun entryBound rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2 label
  obtain ⟨post,entry,steps⟩ := result
  refine ⟨post,naturalCountdown_loop_entry_code arch n,?_,?_⟩
  · simpa [ctxt,name,target,crep,p,body,naturalCountdownCrepBody,wlabWlocExact] using entry
  · simpa [ctxt,name,target,crep,p,body,naturalCountdownCrepBody] using steps

/-- The phase-one natural-countdown fixture supplies the callee execution and
its closed-form visit limit directly. -/
theorem naturalCountdown_fixture_entry_loop (arch : AsmArchitecture) (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let source := panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7))
    let target := loopStateFrom arch source (naturalCountdownHOL n)
    let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := naturalCountdownCrepBody (BitVec.ofNat 64 n)
    let bc := {c with vars := c.vars.updateEq (1,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let body : CrepProgHOL 64 := .dec 2 (.op .sub [.var 1,.const 1]) (.seq (.assign 1 (.var 2)) .skip)
    let tail : CrepProgHOL 64 := .return [.const 0]
    let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while (.var 1) body))) *
      (sizeOf (compileHOLExact bc bl body)+4) + sizeOf (compileHOLExact bc bl tail)
    let bound := (factor+4)*(3 + 8*(6*n+16)+1)
    let code := compileHOLExact c .ln p
    ∃ post,
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+2*bound} = (some (.result [.word 0]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1)+8 := by
  let source := panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7))
  obtain ⟨final,run,bound⟩ := natural_countdown_counted_fixture n range context primitive handler
  have nonzero : (crepStateFrom source (naturalCountdownHOL n)).clock ≠ 0 := by
    simp [source,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,panSimpSourceState,clockedFixtureSource,loweredStateFrom,PanToCrepSteps.noGlobalsLoweredPreCall]
  exact naturalCountdown_entry_loop arch source n (3+8*(6*n+16)) nonzero ⟨final,run⟩ bound

/-- The phase-one prefixed countdown fixture supplies the callee execution and
its closed-form visit limit directly. -/
theorem countdown_fixture_entry_loop (arch : AsmArchitecture) (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let source := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
    let target := loopStateFrom arch source (naturalCountdownHOL n)
    let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := naturalCountdownCrepBody (BitVec.ofNat 64 n)
    let bc := {c with vars := c.vars.updateEq (1,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let body : CrepProgHOL 64 := .dec 2 (.op .sub [.var 1,.const 1]) (.seq (.assign 1 (.var 2)) .skip)
    let tail : CrepProgHOL 64 := .return [.const 0]
    let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while (.var 1) body))) *
      (sizeOf (compileHOLExact bc bl body)+4) + sizeOf (compileHOLExact bc bl tail)
    let bound := (factor+4)*(3 + 8*(6*n+18)+1)
    let code := compileHOLExact c .ln p
    ∃ post,
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+2*bound} = (some (.result [.word 0]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1)+8 := by
  let source := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
  obtain ⟨final,run,bound⟩ := countdown_counted_fixture n range context primitive handler
  have nonzero : (crepStateFrom source (naturalCountdownHOL n)).clock ≠ 0 := by
    simp [source,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,panSimpSourceState,clockedFixtureSource,loweredStateFrom,PanToCrepSteps.noGlobalsLoweredPreCall]
  exact naturalCountdown_entry_loop arch source n (3+8*(6*n+18)) nonzero ⟨final,run⟩ bound

end SteppedFlapjack.Concrete
