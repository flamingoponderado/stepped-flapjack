import SteppedFlapjack.Concrete.BranchLoopSpan
import SteppedFlapjack.LoopLiveSteps.TailEntryShape

set_option maxRecDepth 10000

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps

def branchingLoopEntry : HolLoopProg 64 :=
  .mark (.seq (.mark .skip) (.mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))))

/-- Two generated functions with distinct names share this optimized entry. -/
theorem twoLoopPrograms_entry_code (arch : AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) :
    (64,[],branchingLoopEntry) ∈ twoLoopPrograms arch name callee body := by
  simp only [twoLoopPrograms,List.mem_cons]
  left
  simp [firstLoopName,branchingLoopEntry,optimiseSequence,compileHOLExact,compileExpsHOLExact,
    loopNestedSeqHOL,genTemps,shrinkSequence,shrinkBranch,markAllHOL,
    crepToLoopMakeFuncsExactExecutable,twoPrograms,mkCtxtExact,makeVmapExact,findLabExact,
    HolFiniteMapExact.updateListEq,FUPDATE_LIST,FUPDATE,List.range_succ,fresh]

/-- The actual generated, optimized entry has this concrete tail-call code. -/
theorem branching_loop_entry_code (arch : AsmArchitecture) :
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms branchingHOL) := by
  rw [branching_loop_code]
  exact twoLoopPrograms_entry_code arch _ _ _ (Ne.symm (entryName_fresh branchingHOL))


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

/-- A generated entry reaches a returning zero-argument callee, with eight
wrapper visits in addition to the callee visits. -/
theorem generatedEntry_return {σ : Type} (target post : LoopSemStateFiniteExact 64 σ)
    (code : HolLoopProg 64) (values : List (WordLocW 64)) (limit : Nat)
    (nonzero : target.clock ≠ 0)
    (lookup : findCode (some 65) [] target.code = some (.ln,code))
    (run : evaluate code {decClock target with locals := .ln} = (some (.result values),post))
    (bound : LoopSteps.steps code {decClock target with locals := .ln} ≤ limit) :
    evaluate branchingLoopEntry target = (some (.result values),post) ∧
    LoopSteps.steps branchingLoopEntry target ≤ limit+8 := by
  have callRun : evaluate (.call none (some 65) [] none) target = (some (.result values),post) := by
    rw [evaluate]
    simp only [show getVars [] target = some [] from rfl,lookup,Option.isSome_none,
      Bool.false_eq_true,if_false,nonzero,dite_false]
    rw [run]
  have markedCall : evaluate (.mark (.call none (some 65) [] none)) target =
      (some (.result values),post) := by rw [evaluate,callRun]
  have callSteps := LoopSteps.steps_call_tail (some 65) [] target [] .ln code (by rfl) lookup nonzero
  change LoopSteps.steps (.call none (some 65) [] none) target =
    1 + LoopSteps.steps code {decClock target with locals := .ln} at callSteps
  constructor
  · rw [branchingLoopEntry,evaluate,evaluate_seq]
    have skipRun : evaluate (.mark .skip : HolLoopProg 64) target = (none,target) := by rw [evaluate,evaluate]
    rw [skipRun]
    simp only
    rw [evaluate,evaluate_seq,markedCall]
  · rw [branchingLoopEntry,LoopSteps.steps_mark,LoopSteps.steps_seq]
    have skipStep : LoopSteps.steps (.skip : HolLoopProg 64) target = 1 := LoopSteps.steps_leaf _ _ rfl
    have skipRun : evaluate (.mark .skip : HolLoopProg 64) target = (none,target) := by rw [evaluate,evaluate]
    rw [skipRun]
    simp only
    rw [LoopSteps.steps_mark,skipStep,LoopSteps.steps_mark,LoopSteps.steps_seq]
    rw [markedCall,LoopSteps.steps_mark,callSteps]
    simp only at bound ⊢
    omega

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
  have calleeRun : evaluate (optimiseHOL code) {decClock {target with clock := target.clock+24} with locals := .ln} =
      (some (.result [.word 7]),post) := by rw [entryState]; exact bodyRun
  have calleeBound : LoopSteps.steps (optimiseHOL code) {decClock {target with clock := target.clock+24} with locals := .ln} ≤
      sizeOf (optimiseScalar code)*47 := by rw [entryState]; exact bodyBound
  have entry := generatedEntry_return {target with clock := target.clock+24} post (optimiseHOL code) [.word 7]
    (sizeOf (optimiseScalar code)*47) (by simp) lookup calleeRun calleeBound
  exact ⟨branchCrepEntry_steps,branching_loop_entry_code arch,post,entry.1,entry.2⟩

end SteppedFlapjack.Concrete
