import SteppedFlapjack.Concrete.BranchLoopSpan
import SteppedFlapjack.LoopLiveSteps.TailEntryShape

set_option maxRecDepth 10000

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps

def branchingLoopEntry : HolLoopProg 64 :=
  .mark (.seq (.mark .skip) (.mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))))

/-- The actual generated, optimized entry has this concrete tail-call code. -/
theorem branching_loop_entry_code (arch : AsmArchitecture) :
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms branchingHOL) := by
  rw [branching_loop_code]
  simp only [twoLoopPrograms,List.mem_cons]
  left
  simp [firstLoopName,branchingLoopEntry,optimiseSequence,compileHOLExact,compileExpsHOLExact,
    loopNestedSeqHOL,genTemps,shrinkSequence,shrinkBranch,markAllHOL,
    entryName,crepToLoopMakeFuncsExactExecutable,twoPrograms,mkCtxtExact,makeVmapExact,findLabExact,
    HolFiniteMapExact.updateListEq, FUPDATE_LIST, FUPDATE, List.range_succ]
  have fresh := Ne.symm (entryName_fresh branchingHOL)
  simp only [entryName] at fresh
  simp [fresh]


/-- The entry uses the actual optimized callee from the generated code table. -/
theorem branching_loop_callee_lookup {σ : Type} (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ) :
    findCode (some 65) [] (loopStateFrom arch source branchingHOL).code =
      some (.ln,optimiseHOL (compileHOLExact (witnessLoopContext arch branchingHOL) .ln branchCrepBody)) := by
  have shape : ScalarProgram branchCrepBody :=
    .ite (.cmp .lower (.direct (.const _)) (.direct (.const _)))
      (.ret (.direct (.const _))) (.ret (.direct (.const _)))
  change findCode (some 65) [] (sptFromAList (compileProgHOLExact arch (crepPrograms branchingHOL))) = _
  rw [branching_loop_code]
  simp only [twoLoopPrograms,firstLoopName,findCode]
  rw [optimiseScalar_eq (compile_scalar_program shape _ _)]
  have ctxEq : witnessLoopContext arch branchingHOL =
      mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable
        (twoPrograms (ofString "main") (entryName branchingHOL) branchCrepBody)) 0 := by
    simp [witnessLoopContext,branching_crep_code,twoPrograms,branchCrepBody]
  rw [ctxEq]
  simp only [sptFromAList, sptLookup_sptInsert_ne 64 65 _ _ (by decide), sptLookup_sptInsert_same]
  rfl

/-- The generated entry reaches its optimized callee and returns seven with an
explicit clock and a code-derived bound. -/
theorem branching_entry_loop {σ : Type} (arch : AsmArchitecture) (source : PanSemStateFiniteExact 64 σ) :
    let target := loopStateFrom arch source branchingHOL
    let code := compileHOLExact (witnessLoopContext arch branchingHOL) .ln branchCrepBody
    CrepSteps.steps branchCrepEntry (crepState branchingHOL) = 5 ∧
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms branchingHOL) ∧
    ∃ post,
      evaluate branchingLoopEntry {target with clock := target.clock+24} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+24} ≤ sizeOf (optimiseScalar code)*47 + 8 := by
  let target := loopStateFrom arch source branchingHOL
  let code := compileHOLExact (witnessLoopContext arch branchingHOL) .ln branchCrepBody
  obtain ⟨_,post,_,_,bodyRun,bodyBound⟩ := branching_body_loop arch source
  change evaluate (optimiseHOL code) {target with clock := target.clock+23} = (some (.result [.word 7]),post) at bodyRun
  change LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+23} ≤ sizeOf (optimiseScalar code)*47 at bodyBound
  have locals : target.locals = .ln := rfl
  have entryState : ({decClock {target with clock := target.clock+24} with locals := .ln} : LoopSemStateFiniteExact 64 σ) =
      {target with clock := target.clock+23} := by
    simp [decClock,locals]
  have lookup : findCode (some 65) [] {target with clock := target.clock+24}.code = some (.ln,optimiseHOL code) :=
    branching_loop_callee_lookup arch source
  have callRun : evaluate (.call none (some 65) [] none) {target with clock := target.clock+24} =
      (some (.result [.word 7]),post) := by
    rw [evaluate]
    simp only [show getVars [] {target with clock := target.clock+24} = some [] from rfl,
      lookup,Option.isSome_none,Bool.false_eq_true,if_false]
    have nz : target.clock + 24 ≠ 0 := by omega
    simp only [nz,dite_false,entryState]
    rw [bodyRun]
  have markedCall : evaluate (.mark (.call none (some 65) [] none)) {target with clock := target.clock+24} =
      (some (.result [.word 7]),post) := by rw [evaluate,callRun]
  have callSteps := LoopSteps.steps_call_tail (some 65) [] {target with clock := target.clock+24} [] .ln
    (optimiseHOL code) (by rfl) lookup (by simp)
  refine ⟨branchCrepEntry_steps,branching_loop_entry_code arch,post,?_,?_⟩
  · rw [branchingLoopEntry,evaluate]
    rw [evaluate_seq]
    have skipRun : evaluate (.mark .skip : HolLoopProg 64) {target with clock := target.clock+24} = (none,{target with clock := target.clock+24}) := by rw [evaluate,evaluate]
    rw [skipRun]
    simp only
    rw [evaluate]
    rw [evaluate_seq]
    rw [markedCall]

  · rw [branchingLoopEntry,LoopSteps.steps_mark,LoopSteps.steps_seq]
    have skipStep : LoopSteps.steps (.skip : HolLoopProg 64) {target with clock := target.clock+24} = 1 :=
      LoopSteps.steps_leaf _ _ rfl
    have skipRun : evaluate (.mark .skip : HolLoopProg 64) {target with clock := target.clock+24} = (none,{target with clock := target.clock+24}) := by rw [evaluate,evaluate]
    rw [skipRun]
    simp only
    rw [LoopSteps.steps_mark,skipStep,LoopSteps.steps_mark,LoopSteps.steps_seq]
    rw [markedCall,LoopSteps.steps_mark,callSteps,entryState]
    simp only
    dsimp only [code] at bodyBound ⊢
    omega

end SteppedFlapjack.Concrete
