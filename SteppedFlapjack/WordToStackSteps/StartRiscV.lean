import SteppedFlapjack.WordToStackSteps.StartCall
import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
import SteppedFlapjack.StackToLabSteps.ExplicitSpan
import SteppedFlapjack.WordAllocSteps.WholeTailCode
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackSteps SteppedFlapjack.WordAllocSteps
open Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordDepth
open Flapjack.Compiler.Backend.WordDepthProof Flapjack.Compiler.Backend.BackendProps

set_option maxHeartbeats 1000000 in
private theorem graph_stack_bound {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (n : Nat) (ns : List Nat)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (localSize : s.localsSize = sptLookup n s.stackSize)
    (member : n ∈ ns) (nodup : ns.Nodup)
    (domain : ∀ x, x ∈ ns → (sptLookup x s.code).isSome = true)
    (fits : optionLe
      (optionMap₂ max s.stackMax
        (optionMap₂ (· + ·) (wordSemStackSize s.stack)
          (optionMap₂ max (maxDepthGraphs s.stackSize ns ns s.code s.code)
            (maxDepth s.stackSize (callGraph s.code n ns (sptSize s.code) p)))))
      (some s.stackLimit)) :
    post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
  have sub : sptSubspt s.code s.code := by intro k hk; exact ⟨hk,rfl⟩
  have bound := (maxDepthCallGraphLemma p s res post s.code n ns s.code
    ⟨run,sub,sub,localSize,notError,member,nodup,domain⟩).1
  have trans := optionLe_trans _ _ _ ⟨bound,fits⟩
  have limit := evaluate_stack_limit p s res post run
  cases h : post.stackMax with
  | none => simp [h, optionLe] at trans
  | some m => simpa [h,limit,optionLe] using trans

set_option maxHeartbeats 1000000 in
private theorem graph_start_bound {width : Nat} [NeZero width] {C F : Type}
    (loc frame : Nat) (arg : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (lookup : sptLookup loc s.code = some (1,p)) (frameLookup : sptLookup loc s.stackSize = some frame)
    (args : getVars [0] s = some [arg]) (clock : s.clock ≠ 0)
    (run : evaluate (.call none (some loc) [0] none) s = (res,post)) (notError : res ≠ some .error)
    (fits : let t := callEnv [arg] (some frame) (decClock s)
      optionLe
        (optionMap₂ max t.stackMax
          (optionMap₂ (· + ·) (wordSemStackSize t.stack)
            (optionMap₂ max (maxDepthGraphs t.stackSize [loc] [loc] t.code t.code)
              (maxDepth t.stackSize (callGraph t.code loc [loc] (sptSize t.code) p)))))
        (some t.stackLimit)) :
    post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
  let t := callEnv [arg] (some frame) (decClock s)
  have found : wordSemFindCode (some loc) [arg] s.code s.stackSize = some ([arg],p,some frame) := by
    simp [wordSemFindCode,lookup,frameLookup]
  rw [evaluate] at run
  simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,found,clock,↓reduceDIte,
    Option.some_ne_none,false_and,decide_false,Bool.false_eq_true,if_false] at run
  rcases he : evaluate p t with ⟨r,u⟩
  change (if wordSemBadFunReturn (evaluate p t).1 then
    (some .error,(evaluate p t).2) else evaluate p t) = (res,post) at run
  rw [he] at run
  by_cases bad : wordSemBadFunReturn r = true
  · simp [bad] at run
    exact False.elim (notError run.1.symm)
  · simp only [bad,Bool.false_eq_true,if_false,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    apply graph_stack_bound p t u r loc [loc] he notError
    · simpa [t,WordSemStateFiniteExact.callEnv,decClock] using frameLookup.symm
    · simp
    · simp
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      simp [t,WordSemStateFiniteExact.callEnv,decClock,lookup]
    · exact fits

/-- A completed Word start call reaches RISC-V at an explicit tick bound
and preserves its FFI events when the computed call-graph capacity fits the stack. -/
theorem wordStart_riscv_explicit {F : Type}
    (ac : AsmConfigExact 64) (regs : Nat)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab filtered : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (empty : ∀ i, (coracle i).2.1 = [])
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (source post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result : Option (WordSemResult 64)) (outcome : HolOutcome)
    (related : stateRel ac regs 0 0 source
      ((fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1) [] 0)
    (safe : safeWordCode source) (noAllocCode : WordProps.noAllocCode source.code)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source = (result,post))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (entry : WordLangProgHOL (BitVec 64)) (frame : Nat) (arg : WordLocW 64)
    (entryLookup : sptLookup BvlToBvi.initGlobalsLocation source.code = some (1,entry))
    (entryFrame : sptLookup BvlToBvi.initGlobalsLocation source.stackSize = some frame)
    (entryArgs : getVars [0] source = some [arg]) (entryClock : source.clock ≠ 0)
    (capacity : let t := WordSemStateFiniteExact.callEnv [arg] (some frame) (decClock source)
      optionLe
        (optionMap₂ max t.stackMax
          (optionMap₂ (· + ·) (wordSemStackSize t.stack)
            (optionMap₂ max (maxDepthGraphs t.stackSize [BvlToBvi.initGlobalsLocation]
              [BvlToBvi.initGlobalsLocation] t.code t.code)
              (maxDepth t.stackSize (callGraph t.code BvlToBvi.initGlobalsLocation
                [BvlToBvi.initGlobalsLocation] (sptSize t.code) entry)))))
        (some t.stackLimit))
    (complete : stackEntryClass (result.map compileResult) = .CompleteResult outcome)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (link : LabToTargetSteps.LabExecutionLink filtered lab)
    (tie : LabToTarget.oracleTie mc machine filtered) (rel : LabToTarget.stateRel (mc,labCode,labs,pc) filtered asm machine) :
    let initial := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    let clock := initial.clock + callTableBudget (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * clock
    ∃ finalMachine finalFfi,
      evaluateTargetHOL mc lab.ffi (LabToTargetSteps.labTickBound 4 labCode filtered.codeBuffer *
        stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n) machine =
          (.halt outcome,finalMachine,finalFfi) ∧ finalFfi.ioEvents = post.ffi.ioEvents := by
  dsimp only
  let initial := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
  have emptyInit : StackSteps.emptyCodeOracle initial := by
    intro i
    simpa [initial,fullMakeInit,StackAlloc.makeInit] using empty i
  have stackBound := graph_start_bound BvlToBvi.initGlobalsLocation frame arg entry source post result
    entryLookup entryFrame entryArgs entryClock run notError capacity
  obtain ⟨targetPost,stackRun,ffiEq,_⟩ := wordStack_startCall_exact ac regs BvlToBvi.initGlobalsLocation source post
    initial result related safe noAllocCode emptyInit run notError notTimeout stackBound
  have stackNoError : result.map compileResult ≠ some .error := by
    cases result with
    | none => simp
    | some r => cases r <;> simp_all [compileResult]
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := fullInitStackRiscV_table_explicit
    stackConf dataConf maxHeap sp offset bitmaps code lab filtered saveRegs dataSp coracle empty hA
    (initial.clock + callTableBudget (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source)
    (result.map compileResult) targetPost outcome stackRun stackNoError complete pc mc labCode labs asm machine hmc link tie rel
  exact ⟨finalMachine,finalFfi,machineRun,by rw [events,ffiEq]⟩
/-- Word optimization followed by the Stack and RISC-V compilers preserves
the initial Word run and events at a concrete target tick bound. -/
theorem wordOptimization_riscv_explicit {F : Type}
    (wc : Config) (ac : AsmConfigExact 64) (regs : Nat)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (safety : WordProgramSafety programs)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab filtered : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (empty : ∀ i, (coracle i).2.1 = [])
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (source originalPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result : Option (WordSemResult 64)) (outcome : HolOutcome)
    (codeEq : source.code = sptFromAList (compile wc ac programs).2)
    (related : stateRel ac regs 0 0 source
      ((fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1) [] 0)
    (gc : Compiler.Backend.WordSimp.gcFunConstOk source.gcFun) (stack : source.stack = [])
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {source with code := sptFromAList programs} = (result,originalPost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (entry : WordLangProgHOL (BitVec 64)) (frame : Nat) (arg : WordLocW 64)
    (entryLookup : sptLookup BvlToBvi.initGlobalsLocation source.code = some (1,entry))
    (entryFrame : sptLookup BvlToBvi.initGlobalsLocation source.stackSize = some frame)
    (entryArgs : getVars [0] source = some [arg]) (entryClock : source.clock ≠ 0)
    (capacity : let t := WordSemStateFiniteExact.callEnv [arg] (some frame) (decClock source)
      optionLe
        (optionMap₂ max t.stackMax
          (optionMap₂ (· + ·) (wordSemStackSize t.stack)
            (optionMap₂ max (maxDepthGraphs t.stackSize [BvlToBvi.initGlobalsLocation]
              [BvlToBvi.initGlobalsLocation] t.code t.code)
              (maxDepth t.stackSize (callGraph t.code BvlToBvi.initGlobalsLocation
                [BvlToBvi.initGlobalsLocation] (sptSize t.code) entry)))))
        (some t.stackLimit))
    (complete : stackEntryClass (result.map compileResult) = .CompleteResult outcome)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (link : LabToTargetSteps.LabExecutionLink filtered lab)
    (tie : LabToTarget.oracleTie mc machine filtered) (rel : LabToTarget.stateRel (mc,labCode,labs,pc) filtered asm machine) :
    let initial := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    let clock := initial.clock + callTableBudget (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * clock
    ∃ finalMachine finalFfi,
      evaluateTargetHOL mc lab.ffi (LabToTargetSteps.labTickBound 4 labCode filtered.codeBuffer *
        stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n) machine =
          (.halt outcome,finalMachine,finalFfi) ∧ finalFfi.ioEvents = originalPost.ffi.ioEvents := by
  let orig := {source with code := sptFromAList programs}
  have agree := wholeCompile_start_agrees wc ac programs safety orig BvlToBvi.initGlobalsLocation source.clock rfl gc stack
    (by simpa [orig,run] using notError)
  rw [← codeEq] at agree
  have resultEq : (WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source).1 = result := by
    simpa [orig,run] using agree.1
  have ffiEq : (WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source).2.ffi = originalPost.ffi := by
    simpa [orig,run] using agree.2.1
  have optimizedSafety := wholeCompile_targetSafety wc ac programs safety
  have safe : safeWordCode source := by simpa [safeWordCode,codeEq,WordProgramSafety] using ⟨optimizedSafety.2.1,optimizedSafety.1⟩
  have noAlloc : WordProps.noAllocCode source.code := by simpa [codeEq,WordProgramSafety] using optimizedSafety.2.2
  let post := (WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source).2
  have optimizedRun : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none) source = (result,post) := by
    exact Prod.ext resultEq rfl
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := wordStart_riscv_explicit ac regs stackConf dataConf maxHeap sp
    offset bitmaps code lab filtered saveRegs dataSp coracle empty hA source post result outcome related safe noAlloc
    optimizedRun notError notTimeout entry frame arg entryLookup entryFrame entryArgs entryClock capacity
    complete pc mc labCode labs asm machine hmc link tie rel
  exact ⟨finalMachine,finalFfi,machineRun,by rw [events,ffiEq]⟩

end SteppedFlapjack.WordToStackSteps
