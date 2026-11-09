import SteppedFlapjack.Concrete.WitnessLoopCode
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

/-- The second generated function receives the direct-call label 65. -/
theorem twoPrograms_callee_label (arch : AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) :
    findLabExact (mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (twoPrograms name callee body)) 0) callee = 65 := by
  simp [findLabExact,mkCtxtExact,crepToLoopMakeFuncsExactExecutable,twoPrograms,firstLoopName,
    FUPDATE_LIST,FUPDATE,List.range_succ,fresh]

/-- The actual generated, optimized entry has this concrete tail-call code. -/
theorem branching_loop_entry_code (arch : AsmArchitecture) :
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms branchingHOL) := by
  rw [branching_loop_code]
  exact twoLoopPrograms_entry_code arch _ _ _ (Ne.symm (entryName_fresh branchingHOL))


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

end SteppedFlapjack.Concrete
