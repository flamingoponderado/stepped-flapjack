import SteppedFlapjack.Concrete.WitnessLoopCode
import SteppedFlapjack.Concrete.ScalarEntry
import SteppedFlapjack.Concrete.CrepCountdown
import SteppedFlapjack.Concrete.CountedApplications
import SteppedFlapjack.CrepSteps.TailEntryReturn

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
    (source : PanSemStateFiniteExact 64 σ) (entryFinal : CrepSemHOLState 64 σ) (n limit : Nat)
    (nonzero : (crepStateFrom source (naturalCountdownHOL n)).clock ≠ 0)
    (entryRun : evalCrepSemHOLProgExact (crepStateFrom source (naturalCountdownHOL n))
      (naturalCrepEntry n) = (some (.return [.word 0]),entryFinal))
    (entryBound : CrepSteps.steps (naturalCrepEntry n) (crepStateFrom source (naturalCountdownHOL n)) ≤ limit) :
    let target := loopStateFrom arch source (naturalCountdownHOL n)
    let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := naturalCountdownCrepBody (BitVec.ofNat 64 n)
    let code := compileHOLExact c .ln p
    let bound := scalarOutputEnvelope (loopVisitWeight (optimiseHOL code))*(limit+1)
    ∃ post,
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+2*bound} = (some (.result [.word 0]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*bound} ≤
        loopVisitWeight (optimiseHOL code)*(2*bound+1)+8 ∧
      crepToLoopStateRelExact entryFinal {post with clock := entryFinal.clock} ∧
      crepToLoopMemRelHOLExact entryFinal.memory post.memory entryFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact entryFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt entryFinal.code post.code := by
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
  have scalar : ScalarProgram p := .dec 1 (.direct (.const _)) (.seq
    (.while (.direct (.var _)) (.dec 2 (.direct (.op .sub (.var 1) (.const 1)))
      (.seq (.assign 1 (.direct (.var 2))) .skip))) (.ret (.direct (.const 0))))
  have result := generatedScalar_entry_explicit ctxt name p scalar crep entryFinal target [.word 0] limit
    nonzero found entryRun entryBound rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2 label
  obtain ⟨post,entry,steps,finalState,finalMem,finalGlobals,finalCode⟩ := result
  refine ⟨post,naturalCountdown_loop_entry_code arch n,?_,?_,finalState,finalMem,finalGlobals,finalCode⟩
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
    let code := compileHOLExact c .ln p
    let bound := scalarOutputEnvelope (loopVisitWeight (optimiseHOL code))*(3 + 8*(6*n+16)+1)
    ∃ final post,
      evalCrepSemHOLProgExact (crepStateFrom source (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),final) ∧
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+2*bound} = (some (.result [.word 0]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*bound} ≤
        loopVisitWeight (optimiseHOL code)*(2*bound+1)+8 ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      crepToLoopMemRelHOLExact final.memory post.memory final.memaddrs ∧
      crepToLoopGlobalsRelHOLExact final.globals post.globals ∧
      crepToLoopCodeRelExact ctxt final.code post.code := by
  let source := panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7))
  obtain ⟨final,run,bound⟩ := natural_countdown_counted_fixture n range context primitive handler
  have nonzero : (crepStateFrom source (naturalCountdownHOL n)).clock ≠ 0 := by
    simp [source,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,panSimpSourceState,clockedFixtureSource,loweredStateFrom,PanToCrepSteps.noGlobalsLoweredPreCall]
  obtain ⟨post,compiled,entry,steps,state,mem,globals,codeRel⟩ :=
    naturalCountdown_entry_loop arch source final n (3+8*(6*n+16)) nonzero run bound
  exact ⟨final,post,run,compiled,entry,steps,state,mem,globals,codeRel⟩

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
    let code := compileHOLExact c .ln p
    let bound := scalarOutputEnvelope (loopVisitWeight (optimiseHOL code))*(3 + 8*(6*n+18)+1)
    ∃ final post,
      evalCrepSemHOLProgExact (crepStateFrom source (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),final) ∧
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+2*bound} = (some (.result [.word 0]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*bound} ≤
        loopVisitWeight (optimiseHOL code)*(2*bound+1)+8 ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      crepToLoopMemRelHOLExact final.memory post.memory final.memaddrs ∧
      crepToLoopGlobalsRelHOLExact final.globals post.globals ∧
      crepToLoopCodeRelExact ctxt final.code post.code := by
  let source := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
  obtain ⟨final,run,bound⟩ := countdown_counted_fixture n range context primitive handler
  have nonzero : (crepStateFrom source (naturalCountdownHOL n)).clock ≠ 0 := by
    simp [source,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,panSimpSourceState,clockedFixtureSource,loweredStateFrom,PanToCrepSteps.noGlobalsLoweredPreCall]
  obtain ⟨post,compiled,entry,steps,state,mem,globals,codeRel⟩ :=
    naturalCountdown_entry_loop arch source final n (3+8*(6*n+18)) nonzero run bound
  exact ⟨final,post,run,compiled,entry,steps,state,mem,globals,codeRel⟩

end SteppedFlapjack.Concrete
