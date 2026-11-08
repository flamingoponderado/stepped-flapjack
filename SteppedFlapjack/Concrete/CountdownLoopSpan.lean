import SteppedFlapjack.Concrete.WitnessLoopCode
import SteppedFlapjack.Concrete.BranchEntryLoop
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

/-- The natural countdown's tail call looks up its actual optimized callee. -/
theorem naturalCountdown_loop_callee_lookup {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) (n : Nat) :
    let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    findCode (some 65) [] (loopStateFrom arch source (naturalCountdownHOL n)).code =
      some (.ln,optimiseHOL (compileHOLExact c .ln (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) := by
  have shape : ScalarProgram (naturalCountdownCrepBody (BitVec.ofNat 64 n)) := .dec _ (.direct (.const _)) (.seq
    (.while (.direct (.var _)) (.dec _ (.direct (.op .sub (.var _) (.const _)))
      (.seq (.assign _ (.direct (.var _))) .skip))) (.ret (.direct (.const _))))
  change findCode (some 65) [] (sptFromAList (compileProgHOLExact arch (crepPrograms (naturalCountdownHOL n)))) = _
  rw [naturalCountdown_loop_code]
  simp only [twoLoopPrograms,firstLoopName,findCode]
  rw [optimiseScalar_eq (compile_scalar_program shape _ _)]
  have ctxEq : witnessLoopContext arch (naturalCountdownHOL n) =
      mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable
        (twoPrograms (ofString "main") (entryName (naturalCountdownHOL n))
          (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) 0 := by
    simp [witnessLoopContext,natural_countdown_crep_code,twoPrograms]
  rw [ctxEq]
  simp only [sptFromAList, sptLookup_sptInsert_ne 64 65 _ _ (by decide), sptLookup_sptInsert_same]
  simp [ctxtFcExact,mkCtxtExact,makeVmapExact,sptFromAList,HolFiniteMapExact.updateListEq,HolFiniteMapExact.updateList,FUPDATE_LIST]

/-- A returning natural-countdown entry gives an optimized callee run with an
explicit bound derived from the phase-one entry-visit limit. -/
theorem naturalCountdown_callee_loop {σ : Type} (arch : AsmArchitecture)
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
      (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail)
    let bound := (factor+4)*(limit+1)
    let code := compileHOLExact c .ln p
    ∃ post,
      evaluate (optimiseHOL code) {decClock target with locals := .ln, clock := (decClock target).clock+2*bound} =
        (some (.result [.word 0]),post) ∧
      LoopSteps.steps (optimiseHOL code) {decClock target with locals := .ln, clock := (decClock target).clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1) := by
  let crep := crepStateFrom source (naturalCountdownHOL n)
  let target := loopStateFrom arch source (naturalCountdownHOL n)
  let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p := naturalCountdownCrepBody (BitVec.ofNat 64 n)
  have found : crep.code.lookup (entryName (naturalCountdownHOL n)) = some ([],p) := by
    have h := generated_callee_lookup (naturalCountdownHOL n) p (natural_countdown_crep_code n)
    simpa [crep,crepState,crepStateFrom,PanToCrepSteps.concreteDeclCrepState] using h
  obtain ⟨entryFinal,entryRun⟩ := entryRun
  have startRun : evalCrepSemHOLProgExact crep (.seq .skip (.call none (entryName (naturalCountdownHOL n)) [])) =
      (some (.return [.word 0]),entryFinal) := entryRun
  obtain ⟨sourceFinal,calleeRun,calleeBound⟩ := CrepSteps.tail_entry_return_inv crep entryFinal
    (entryName (naturalCountdownHOL n)) p [.word 0] limit found nonzero startRun entryBound
  have rel := loopStateFrom_relations arch source (naturalCountdownHOL n)
  have codeLocals := naturalCountdown_loop_code_locals arch source n
  have calleeRel := tailCall_nil_entry_relations ctxt .ln crep target (entryName (naturalCountdownHOL n)) p
    rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2 found
  have bodyShape : BranchProgram (.dec 2 (.op .sub [.var 1,.const 1]) (.seq (.assign 1 (.var 2)) .skip) : CrepProgHOL 64) :=
    .dec (.op .sub (.var 1) (.const 1)) (.seq (.expr (.assign 1 (.var 2))) (.expr (.leaf .skip)))
  have tailShape : BranchProgram (.return [.const 0] : CrepProgHOL 64) := .expr (.returnOne (.const 0))
  have scalar : ScalarProgram p := .dec 1 (.direct (.const _)) (.seq
    (.while (.direct (.var _)) (.dec 2 (.direct (.op .sub (.var 1) (.const 1)))
      (.seq (.assign 1 (.direct (.var 2))) .skip))) (.ret (.direct (.const 0))))
  have result := directDecl_whileThenBranch_explicit 1 (.const (BitVec.ofNat 64 n)) (.const _) (.var 1)
    _ _ (.var 1) bodyShape tailShape scalar c .ln _ sourceFinal _ _ limit calleeRun calleeBound
    (.return _) calleeRel.1 calleeRel.2.1 calleeRel.2.2.1 calleeRel.2.2.2.1 calleeRel.2.2.2.2
  obtain ⟨post,run,bound,_,_,_,_⟩ := result
  exact ⟨post,by simpa [p,naturalCountdownCrepBody,c,ctxt,target,resultToLoop,wlabWlocExact] using run,by simpa [p,naturalCountdownCrepBody,c,ctxt,target] using bound⟩
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
      (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail)
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
  have targetNonzero : (loopStateFrom arch source (naturalCountdownHOL n)).clock ≠ 0 := by
    have relation := (loopStateFrom_relations arch source (naturalCountdownHOL n)).1.2.2.1
    omega
  obtain ⟨post,calleeRun,calleeBound⟩ := naturalCountdown_callee_loop arch source n (3+8*(6*n+16)) nonzero ⟨final,run⟩ bound
  let target := loopStateFrom arch source (naturalCountdownHOL n)
  change target.clock ≠ 0 at targetNonzero
  let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p := naturalCountdownCrepBody (BitVec.ofNat 64 n)
  let bc := {c with vars := c.vars.updateEq (1,c.vmax+1), vmax := c.vmax+1}
  let bl := sptInsert (c.vmax+1) () .ln
  let body : CrepProgHOL 64 := .dec 2 (.op .sub [.var 1,.const 1]) (.seq (.assign 1 (.var 2)) .skip)
  let tail : CrepProgHOL 64 := .return [.const 0]
  let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while (.var 1) body))) *
    (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail)
  let budget := (factor+4)*(3+8*(6*n+16)+1)
  let code := compileHOLExact c .ln p
  have clockEq : ({decClock {target with clock := target.clock+2*budget} with locals := .ln} : LoopSemStateFiniteExact 64 Unit) =
      {decClock target with locals := .ln, clock := (decClock target).clock+2*budget} := by
    simp only [decClock]
    congr 1
    omega
  have lookup : findCode (some 65) [] {target with clock := target.clock+2*budget}.code =
      some (.ln,optimiseHOL code) := naturalCountdown_loop_callee_lookup arch source n
  have cr : evaluate (optimiseHOL code) {decClock {target with clock := target.clock+2*budget} with locals := .ln} =
      (some (.result [.word 0]),post) := by rw [clockEq]; exact calleeRun
  have cb : LoopSteps.steps (optimiseHOL code) {decClock {target with clock := target.clock+2*budget} with locals := .ln} ≤
      sizeOf (optimiseScalar code)*(2*budget+1) := by rw [clockEq]; exact calleeBound
  have entry := generatedEntry_return {target with clock := target.clock+2*budget} post (optimiseHOL code) [.word 0]
    (sizeOf (optimiseScalar code)*(2*budget+1)) (by simp only; omega) lookup cr cb
  exact ⟨post,naturalCountdown_loop_entry_code arch n,entry.1,entry.2⟩

end SteppedFlapjack.Concrete
