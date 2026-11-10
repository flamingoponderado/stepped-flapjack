import SteppedFlapjack.LoopToWordSteps.FullInitNativeSetup
import Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileBitmaps

/-! Derive native Word-to-Stack initialization from full initialization. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordSimp
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- The standard full-initialization assumptions ensure that the optional
Stack initializer succeeds, even though the machine context stores only the
initialized Stack state. -/
theorem FullInitStackContext.initializer_succeeds {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    ∃ initialized,
      (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.bitmaps
        backend.inputCode backend.lab backend.saveRegs backend.dataSp backend.coracle).2 = some initialized := by
  have bundles := And.intro (dischargeThese_s2 backend.initAssumptions) (propagateThese_s2 backend.initAssumptions)
  obtain ⟨initialized,opt,_⟩ := InitSemantics.makeInitSemantics backend.stackConf.jump backend.offset
    (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.sp BvlToBvi.initGlobalsLocation
    (coracle1 backend.coracle) (code1 backend.dataConf backend.inputCode)
    (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode
      backend.lab backend.saveRegs backend.coracle) backend.bitmaps backend.dataSp bundles
  exact ⟨initialized,by simpa only [fullMakeInit_eq] using opt⟩

/-- The initializer takes its heap base from register 2 and preserves input
memory on the initialized heap domain. -/
theorem initOpt_heap_data {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maxHeap pointer start : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : List (Nat × HolProg width)) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (hyp : InitMake.dischargeThese jump bounds generateGc maxHeap pointer start oracle code s ∧
      InitMake.propagateThese s bitmaps dataSpace)
    (initialized : StackSemStateFiniteExact width C F)
    (opt : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer
      (sptFromAList code) s = some initialized) :
    ∃ current, s.regs.lookup 2 = some (.word current) ∧
      initialized.store.lookup .currHeap = some (.word current) ∧
      ∀ address, initialized.mdomain address = true → initialized.memory address = s.memory address := by
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := hyp
  have pre : InitCodePre.initCodePre pointer bitmaps dataSpace s := by
    have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
      rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
    rw [sub] at heap
    exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
      m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  have codeRel := InitCodeRelation.impCodeRel jump bounds generateGc maxHeap pointer start code s.code ⟨every, codeEq⟩
  have err : sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) := by
    rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup, stackErrLab]
  have main := InitCodeCorrect.initCodeThm generateGc maxHeap pointer bitmaps dataSpace s jump bounds
    (sptFromAList code) oracle ⟨pre,codeRel,oracleEq,oracleBound,err,maxOk⟩
  cases run : StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
  | mk result post =>
    cases result with
    | some r => simp [run] at main
    | none =>
      simp only [run] at main
      obtain ⟨⟨current,_,_,hread,_,hpost,_⟩,rel,_,prop,_,_,memEq⟩ := main
      have opt' : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer
          (sptFromAList code) s = some (InitReduce.initReduce generateGc jump bounds pointer
            (sptFromAList code) bitmaps dataSpace oracle post) := by
        simp [InitMake.makeInitOpt,run,prop]
      have eq : initialized = InitReduce.initReduce generateGc jump bounds pointer
          (sptFromAList code) bitmaps dataSpace oracle post := Option.some.inj (opt.symm.trans opt')
      have relcur : post.regs.lookup (pointer + 2) =
          (InitReduce.initReduce generateGc jump bounds pointer (sptFromAList code) bitmaps dataSpace oracle post).store.lookup .currHeap := by
        exact rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨current,hread,by rw [eq,← relcur,hpost],?_⟩
      intro address domain
      rw [eq] at domain ⊢
      have member : SetSep.fun2Set (s.memory, fun a =>
          (InitReduce.initReduce generateGc jump bounds pointer (sptFromAList code) bitmaps dataSpace oracle post).mdomain a = true)
          (address,s.memory address) := (SetSep.fun2SetThm _ _ _ _).mpr ⟨rfl,domain⟩
      rw [memEq] at member
      have value := (SetSep.fun2SetThm _ _ _ _).mp member
      exact value.1


/-- Full initialization takes the heap base from the Lab register corresponding
to Stack register 2 and preserves Lab memory on the initialized heap domain. -/
theorem FullInitStackContext.heap_base_and_memory_lab {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    ∃ current, backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2) = .word current ∧
      stack.store.lookup .currHeap = some (.word current) ∧
      ∀ address, stack.mdomain address = true → stack.memory address = backend.lab.memory address := by
  obtain ⟨initialized,fullOpt⟩ := backend.initializer_succeeds
  simp only [fullMakeInit_eq] at fullOpt
  have bundles := And.intro (dischargeThese_s2 backend.initAssumptions) (propagateThese_s2 backend.initAssumptions)
  obtain ⟨current,read,store,memory⟩ := initOpt_heap_data backend.stackConf.jump backend.offset
    (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.sp BvlToBvi.initGlobalsLocation
    (coracle1 backend.coracle) (code1 backend.dataConf backend.inputCode)
    (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode
      backend.lab backend.saveRegs backend.coracle) backend.bitmaps backend.dataSp bundles initialized fullOpt
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bij⟩ := backend.initAssumptions
  have labRead := s2_regs_lookup (stackConf := backend.stackConf) (dataConf := backend.dataConf)
    (maxHeap := backend.maxHeap) (sp := backend.sp) (offset := backend.offset) (code := backend.inputCode)
    (t := backend.lab) (saveRegs := backend.saveRegs) (coracle := backend.coracle) bij (i := 2) (by simp)
  have stateEq := backend.stackEq
  rw [fullMakeInit_eq] at stateEq
  have stateEq' : stack = StackAlloc.makeInit backend.dataConf (sptFromAList backend.inputCode) backend.coracle initialized := by
    simpa [InitMake.makeInitAny,fullOpt] using stateEq
  refine ⟨current,?_,?_,?_⟩
  · rw [labRead] at read
    exact Option.some.inj read
  · simpa [stateEq',StackAlloc.makeInit] using store
  · intro address domain
    have domain' : initialized.mdomain address = true := by simpa [stateEq',StackAlloc.makeInit] using domain
    have fact := memory address domain'
    simpa [stateEq',StackAlloc.makeInit,s2,s3,StackNames.makeInit,StackToLab.Proofs.MakeInit.makeInit] using fact

/-- Heap-half length calculated by the original initializer from the three
Lab pointer registers. -/
noncomputable def FullInitStackContext.labHeapLength {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) : BitVec 64 :=
  let reg := fun n => wordSemTheWord (backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames n))
  BitVec.ofNat 64 (InitLimits.getStackHeapLimit backend.maxHeap (reg 2,reg 3,reg 4)).2 * bytesInWord 64

/-- The initialized heap length is the original limit calculation on the
Lab pointer registers. -/
theorem FullInitStackContext.heap_length_lab {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    stack.store.lookup .heapLength = some (.word backend.labHeapLength) := by
  obtain ⟨initialized,fullOpt⟩ := backend.initializer_succeeds
  simp only [fullMakeInit_eq] at fullOpt
  obtain ⟨_,_,prop⟩ := InitAny.makeInitOpt_eq_some fullOpt
  have lim := prop
  rcases lim with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,limitOk,_⟩
  have length := limitOk.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bij⟩ := backend.initAssumptions
  have read2 := s2_regs_lookup (stackConf := backend.stackConf) (dataConf := backend.dataConf)
    (maxHeap := backend.maxHeap) (sp := backend.sp) (offset := backend.offset) (code := backend.inputCode)
    (t := backend.lab) (saveRegs := backend.saveRegs) (coracle := backend.coracle) bij (i := 2) (by simp)
  have read3 := s2_regs_lookup (stackConf := backend.stackConf) (dataConf := backend.dataConf)
    (maxHeap := backend.maxHeap) (sp := backend.sp) (offset := backend.offset) (code := backend.inputCode)
    (t := backend.lab) (saveRegs := backend.saveRegs) (coracle := backend.coracle) bij (i := 3) (by simp)
  have read4 := s2_regs_lookup (stackConf := backend.stackConf) (dataConf := backend.dataConf)
    (maxHeap := backend.maxHeap) (sp := backend.sp) (offset := backend.offset) (code := backend.inputCode)
    (t := backend.lab) (saveRegs := backend.saveRegs) (coracle := backend.coracle) bij (i := 4) (by simp)
  have pointers : InitLimits.readPointers (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp
      backend.offset backend.inputCode backend.lab backend.saveRegs backend.coracle) =
      (wordSemTheWord (backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2)),
       wordSemTheWord (backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 3)),
       wordSemTheWord (backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 4))) := by
    simp [InitLimits.readPointers,read2,read3,read4,holThe]
  rw [pointers] at length
  have stateEq := backend.stackEq
  rw [fullMakeInit_eq] at stateEq
  have stateEq' : stack = StackAlloc.makeInit backend.dataConf (sptFromAList backend.inputCode) backend.coracle initialized := by
    simpa [InitMake.makeInitAny,fullOpt] using stateEq
  simpa [stateEq',StackAlloc.makeInit,FullInitStackContext.labHeapLength] using length

/-- Successful full initialization provides the two contiguous, separated
heap regions and the corresponding Stack store entries. -/
theorem FullInitStackContext.heap_shape {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    ∃ (current other : BitVec 64) (length : Nat),
      stack.store.lookup .currHeap = some (.word current) ∧
      stack.store.lookup .nextFree = some (.word current) ∧
      stack.store.lookup .endOfHeap = some (.word other) ∧
      stack.store.lookup .heapLength = some (.word (BitVec.ofNat 64 length * bytesInWord 64)) ∧
      other = current + bytesInWord 64 * BitVec.ofNat 64 length ∧
      SetSep.star (Misc.wordListExists current length) (Misc.wordListExists other length)
        (SetSep.fun2Set (stack.memory, fun address => stack.mdomain address = true)) := by
  obtain ⟨initialized,fullOpt⟩ := backend.initializer_succeeds
  simp only [fullMakeInit_eq] at fullOpt
  obtain ⟨_,_,prop⟩ := InitAny.makeInitOpt_eq_some fullOpt
  rcases prop with ⟨current,other,bitmap,length,hcurrent,hnext,_,hend,_,_,hlength,rest⟩
  rcases rest with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hother,_,_,_,_,_,hheap⟩
  have eq := backend.stackEq
  rw [fullMakeInit_eq] at eq
  have stateEq : stack = StackAlloc.makeInit backend.dataConf (sptFromAList backend.inputCode) backend.coracle initialized := by
    simpa [InitMake.makeInitAny,fullOpt] using eq
  refine ⟨current,other,length,?_,?_,?_,?_,hother,?_⟩
  · simpa [stateEq,StackAlloc.makeInit] using hcurrent
  · simpa [stateEq,StackAlloc.makeInit] using hnext
  · simpa [stateEq,StackAlloc.makeInit] using hend
  · simpa [stateEq,StackAlloc.makeInit] using hlength
  · simpa [stateEq,StackAlloc.makeInit] using hheap

/-- The heap end is the current pointer plus the Lab-derived half length. -/
theorem FullInitStackContext.heap_end_lab {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (current : BitVec 64) (hcurrent : stack.store.lookup .currHeap = some (.word current)) :
    stack.store.lookup .endOfHeap = some (.word (current + backend.labHeapLength)) := by
  obtain ⟨c,other,n,hc,_,hend,hlen,offset,_⟩ := backend.heap_shape
  have ec : c = current := by simpa [hcurrent,eq_comm] using hc
  have en : BitVec.ofNat 64 n * bytesInWord 64 = backend.labHeapLength := by
    simpa [backend.heap_length_lab,eq_comm] using hlen
  subst c
  rw [offset] at hend
  simpa [en,mul_comm] using hend

/-- A separated word list contains exactly the addresses generated by the
initializer's address-range function, even with modular address arithmetic. -/
theorem wordList_heap_domain {width : Nat} [NeZero width] {β : Type}
    (values : List β) (base : BitVec width) (heap : (BitVec width × β) → Prop)
    (h : Misc.wordList base values heap) (address : BitVec width) :
    (∃ value, heap (address,value)) ↔ addresses base values.length address := by
  induction values generalizing base heap with
  | nil =>
    simp only [Misc.wordList,SetSep.emp] at h
    subst heap
    simp [addresses]
  | cons value values ih =>
    simp only [Misc.wordList,SetSep.star] at h
    obtain ⟨left,right,⟨partition,_⟩,one,rest⟩ := h
    simp only [SetSep.one] at one
    have member (entry : BitVec width × β) : heap entry ↔ left entry ∨ right entry := by
      rw [← partition]
    simp only [List.length_cons,addresses]
    constructor
    · rintro ⟨v,hv⟩
      rcases (member _).mp hv with hl | hr
      · left
        rw [one] at hl
        exact congrArg Prod.fst hl
      · exact Or.inr ((ih _ _ rest).mp ⟨v,hr⟩)
    · intro h
      rcases h with equal | tail
      · subst address
        exact ⟨value,(member _).mpr (Or.inl (by rw [one]))⟩
      · obtain ⟨v,hv⟩ := (ih _ _ rest).mpr tail
        exact ⟨v,(member _).mpr (Or.inr hv)⟩

/-- Successful initialization's Stack memory domain is exactly the address
range occupied by its two adjacent heap halves. -/
theorem FullInitStackContext.heap_domain {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    ∃ (current other : BitVec 64) (length : Nat),
      stack.store.lookup .currHeap = some (.word current) ∧
      stack.store.lookup .endOfHeap = some (.word other) ∧
      stack.store.lookup .heapLength = some (.word (BitVec.ofNat 64 length * bytesInWord 64)) ∧
      other = current + bytesInWord 64 * BitVec.ofNat 64 length ∧
      (BitVec.ofNat 64 length * bytesInWord 64).toNat / 8 = length ∧
      ∀ address, stack.mdomain address = true ↔ addresses current (length + length) address := by
  obtain ⟨current,other,length,curr,_,last,len,otherEq,heap⟩ := backend.heap_shape
  rw [otherEq,← WordListMemory.wordListExistsAdd] at heap
  obtain ⟨values,assertion⟩ := heap
  obtain ⟨wordList,lengthEq⟩ := (WordListExists.starCond _ _ _).mp assertion
  have framed : SetSep.star SetSep.emp (Misc.wordList current values)
      (SetSep.fun2Set (stack.memory, fun a => stack.mdomain a = true)) := by
    refine ⟨(fun _ => False),_,?_,rfl,wordList⟩
    simp [SetSep.split]
  have bound := InitCodeCorrect.wordListNoWrap (width := 64) (by simp [goodDimindex])
    SetSep.emp current values stack.memory (fun a => stack.mdomain a = true) framed
  rw [lengthEq] at bound
  have small : length * 8 < 2 ^ 64 := by omega
  have count : (BitVec.ofNat 64 length * bytesInWord 64).toNat / 8 = length := by
    simp only [BitVec.toNat_mul,BitVec.toNat_ofNat,bytesInWord]
    have lsmall : length < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt lsmall]
    norm_num at *
    omega
  refine ⟨current,other,length,curr,last,len,otherEq,count,?_⟩
  intro address
  have graph : stack.mdomain address = true ↔
      ∃ value, SetSep.fun2Set (stack.memory, fun a => stack.mdomain a = true) (address,value) := by
    constructor
    · intro domain
      exact ⟨stack.memory address,(SetSep.fun2SetThm _ _ _ _).mpr ⟨rfl,domain⟩⟩
    · rintro ⟨value,member⟩
      exact ((SetSep.fun2SetThm _ _ _ _).mp member).2
  rw [graph,wordList_heap_domain values current _ wordList address,lengthEq]

/-- The initialized domain is determined by its current and end pointers. -/
theorem FullInitStackContext.heap_domain_of_pointers {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (current other : BitVec 64)
    (hcurrent : stack.store.lookup .currHeap = some (.word current))
    (hother : stack.store.lookup .endOfHeap = some (.word other)) :
    ∀ address, stack.mdomain address = true ↔
      addresses current (((other - current).toNat / 8) + ((other - current).toNat / 8)) address := by
  obtain ⟨c,o,n,hc,ho,_,offset,count,domain⟩ := backend.heap_domain
  have ec : c = current := by simpa [hcurrent,eq_comm] using hc
  have eo : o = other := by simpa [hother,eq_comm] using ho
  subst c
  subst o
  have diff : other - current = BitVec.ofNat 64 n * bytesInWord 64 := by
    rw [offset]
    simp [mul_comm]
  rw [diff,count]
  exact domain

/-- The initialized heap length is determined by its current and end pointers. -/
theorem FullInitStackContext.heap_length_of_pointers {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (current other : BitVec 64)
    (hcurrent : stack.store.lookup .currHeap = some (.word current))
    (hother : stack.store.lookup .endOfHeap = some (.word other)) :
    stack.store.lookup .heapLength = some (.word (other - current)) := by
  obtain ⟨c,o,n,hc,_,ho,hn,offset,_⟩ := backend.heap_shape
  have ec : c = current := by simpa [hcurrent,eq_comm] using hc
  have eo : o = other := by simpa [hother,eq_comm] using ho
  subst c
  subst o
  rw [offset]
  simpa [BitVec.add_comm, BitVec.add_sub_cancel, mul_comm] using hn

/-- Full initialization supplies the native entry-state validity relation
when the native oracle obeys the compiler's conventions and generates the
Stack oracle. The bitmap header and available register count are explicit. -/
theorem FullInitStackContext.nativeInitOk {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (ac : AsmConfigExact 64)
    (wordOracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (tail : List (BitVec 64))
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (bitmaps : backend.bitmaps = 4 :: tail)
    (oracleValid : ∀ n,
      let ((bm0, _), progs) := wordOracle n
      progs.all (fun p => postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
      progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
      (n = 0 → bm0 = backend.bitmaps.length))
    (oracleEq : backend.coracle = (fun n =>
      let ((bm0,cfg),progs) := wordOracle n
      let (compiled,_,bm) := compileWordToStackNative ac false (ac.regCount-(5+ac.avoidRegs.length)) progs (.nil,bm0)
      (cfg,compiled,appListAppend bm.1))) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack wordOracle := by
  obtain ⟨initialized,fullOpt⟩ := backend.initializer_succeeds
  have fullPair : fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode backend.lab backend.saveRegs backend.dataSp backend.coracle =
        (stack,some initialized) := Prod.ext backend.stackEq.symm fullOpt
  exact Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState.impInitStateOk
    ⟨registers,bitmaps,backend.initAssumptions.1,oracleValid,oracleEq,fullPair⟩


/-- Full initialization installs the supplied Stack code and bitmaps. -/
theorem FullInitStackContext.stack_code_and_bitmaps {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    stack.code = sptFromAList backend.inputCode ∧ stack.bitmaps = backend.bitmaps := by
  obtain ⟨initialized,fullOpt⟩ := backend.initializer_succeeds
  have codeEq := congrArg (fun s : StackSemStateFiniteExact 64 LabToTarget.Config F => s.code) backend.stackEq
  have bitmapEq := congrArg (fun s : StackSemStateFiniteExact 64 LabToTarget.Config F => s.bitmaps) backend.stackEq
  constructor
  · rw [codeEq,fullMakeInit_eq]
    rfl
  · rw [bitmapEq,fullMakeInit_eq]
    change (InitMake.makeInitAny (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.bitmaps backend.dataSp
      (coracle1 backend.coracle) backend.stackConf.jump backend.offset backend.sp (sptFromAList (code1 backend.dataConf backend.inputCode))
      (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode backend.lab backend.saveRegs backend.coracle)).bitmaps = backend.bitmaps
    rw [InitAny.makeInitAnyBitmaps]
    simp only [fullMakeInit_eq] at fullOpt
    simp [fullOpt]


/-- The full initializer and an actual native compiler output provide the
Stack code and bitmap-prefix premises used by the source compiler bundle. -/
theorem FullInitStackContext.nativeCompilerCode {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : backend.inputCode = (compileNative ac false programs).2.2.2)
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps) :
    stack.code = sptFromAList (compileNative ac false programs).2.2.2 ∧
    (compileNative ac false programs).1.IsPrefix stack.bitmaps := by
  obtain ⟨code,bitmaps⟩ := backend.stack_code_and_bitmaps
  exact ⟨by simpa only [codeEq] using code,by simpa only [bitmaps] using bitmapPrefix⟩


/-- A bitmap table extending the actual native compiler output has the
header required by the native initialization proof. -/
theorem FullInitStackContext.nativeBitmapHeader {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps) :
    ∃ tail, backend.bitmaps = 4 :: tail := by
  rcases compiled : compileNative ac false programs with ⟨bitmaps,config,rest⟩
  have header := (compileWordToStackBitmaps ac programs bitmaps config rest compiled).1
  rw [compiled] at bitmapPrefix
  cases bitmaps with
  | nil => simp at header
  | cons head tail =>
    simp only at header
    subst head
    obtain ⟨suffix,eq⟩ := bitmapPrefix
    exact ⟨tail ++ suffix,by simpa using eq.symm⟩


/-- Native initialization validity follows from the full initializer and
actual bitmap prefix, with only register and oracle compatibility conditions. -/
theorem FullInitStackContext.nativeInitOk_of_compiled {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wordOracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (oracleValid : ∀ n,
      let ((bm0, _), progs) := wordOracle n
      progs.all (fun p => postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
      progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
      (n = 0 → bm0 = backend.bitmaps.length))
    (oracleEq : backend.coracle = (fun n =>
      let ((bm0,cfg),progs) := wordOracle n
      let (compiled,_,bm) := compileWordToStackNative ac false (ac.regCount-(5+ac.avoidRegs.length)) progs (.nil,bm0)
      (cfg,compiled,appListAppend bm.1))) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack wordOracle := by
  obtain ⟨tail,header⟩ := backend.nativeBitmapHeader ac programs bitmapPrefix
  exact backend.nativeInitOk ac wordOracle tail registers header oracleValid oracleEq


/-- An oracle that never installs code and begins at the supplied bitmap
length. Its configuration is carried through unchanged. -/
def emptyNativeWordOracle (bitmapLength : Nat) (cfg : LabToTarget.Config) :
    Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  fun _ => ((bitmapLength,cfg),[])

/-- The empty Word oracle satisfies all compiler conventions and translates
to the empty Stack oracle. -/
theorem emptyNativeWordOracle_compatible (ac : AsmConfigExact 64) (bitmapLength : Nat)
    (cfg : LabToTarget.Config) :
    (∀ n,
      let ((bm0, _), progs) := emptyNativeWordOracle bitmapLength cfg n
      progs.all (fun p => postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
      progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
      (n = 0 → bm0 = bitmapLength)) ∧
    (fun n =>
      let ((bm0,c),progs) := emptyNativeWordOracle bitmapLength cfg n
      let (compiled,_,bm) := compileWordToStackNative ac false (ac.regCount-(5+ac.avoidRegs.length)) progs (.nil,bm0)
      (c,compiled,appListAppend bm.1)) = (fun _ => (cfg,[],[])) := by
  constructor
  · intro n
    simp [emptyNativeWordOracle]
  · funext n
    simp [emptyNativeWordOracle,compileWordToStackNative,appListAppend,appendAux]

/-- For a Stack oracle that never installs code, all Word-oracle convention
and translation obligations follow from the empty oracle construction. -/
theorem FullInitStackContext.nativeInitOk_emptyOracle {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (cfg : LabToTarget.Config)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (stackOracle : backend.coracle = fun _ => (cfg,[],[])) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack (emptyNativeWordOracle backend.bitmaps.length cfg) := by
  have compat := emptyNativeWordOracle_compatible ac backend.bitmaps.length cfg
  apply backend.nativeInitOk_of_compiled ac programs _ registers bitmapPrefix compat.1
  exact stackOracle.trans compat.2.symm

end SteppedFlapjack.LoopToWordSteps
