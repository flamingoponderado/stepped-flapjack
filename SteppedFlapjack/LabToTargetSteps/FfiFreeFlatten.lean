import Flapjack.Compiler.Backend.StackToLab.Proofs.NoShmemop
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo

/-! FFI exclusion for Stack-to-Lab flattening and FFI-name collection. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.LabToTarget

/-- Absence of FFI instructions in a Stack program, including continuations. -/
def stackNoFfi {width : Nat} [NeZero width] : HolProg width → Bool
  | .call ret _ handler =>
      (match ret with | some (body,_,_,_) => stackNoFfi body | none => true) &&
      (match handler with | some (body,_,_) => stackNoFfi body | none => true)
  | .seq a b => stackNoFfi a && stackNoFfi b
  | .ite _ _ _ a b => stackNoFfi a && stackNoFfi b
  | .loop body => stackNoFfi body
  | .ffi _ _ _ _ _ _ => false
  | _ => true

/-- Test whether a Lab line is not an external call. -/
def labLineNoFfi {width : Nat} [NeZero width] : LabSem.LabLineHOL width → Bool
  | .labAsm (.callFFI _) _ _ _ => false
  | _ => true

set_option maxHeartbeats 1000000 in
/-- Flattening an FFI-free Stack program emits no external-call lines. -/
theorem flatten_noFfi {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n m : Nat) (cs bs : List Nat), stackNoFfi p = true →
      (appListAppend (StackToLab.flattenHOL t p n m cs bs).1).all labLineNoFfi = true := by
  intro t p n m cs bs
  induction t, p, m, cs, bs using StackToLab.flattenHOL.induct n
  all_goals
    intro hns
    rw [StackToLab.flattenHOL]
    try simp (config := { zetaDelta := true }) only [*] at *
  all_goals (try split) <;>
    (try simp only [FlattenCorrect.appListAppendList, FlattenCorrect.appListAppendAppend,
      stackNoFfi, Bool.and_eq_true, labLineNoFfi, compileJumpHOL, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.true_and] at hns ⊢)
  all_goals (repeat' split) <;> (try simp only [FlattenCorrect.appListAppendList,
      FlattenCorrect.appListAppendAppend, Bool.and_eq_true, labLineNoFfi, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.true_and] at hns ⊢)
  all_goals (try obtain ⟨hns1, hns2⟩ := hns)
  all_goals (repeat' constructor) <;> (try solve_by_elim)
  all_goals rename_i h; split at h <;> simp at h

/-- A section list containing no external-call lines has no FFI names. -/
theorem findFfiNames_of_noFfi {width : Nat} [NeZero width] (code : LabSem.LabProgHOL width)
    (safe : ∀ sec ∈ code, sec.lines.all labLineNoFfi = true) : findFfiNames code = [] := by
  fun_induction findFfiNames code with
  | case1 => rfl
  | case2 k rest ih =>
    apply ih
    intro sec hm
    exact safe sec (List.mem_cons_of_mem _ hm)
  | case3 k xs rest name pos bytes len ih =>
    have h := safe ⟨k,.labAsm (.callFFI name) pos bytes len :: xs⟩ List.mem_cons_self
    simp [labLineNoFfi] at h
  | case4 k x xs rest hx ih =>
    apply ih
    intro sec hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · have h := safe ⟨k,x::xs⟩ List.mem_cons_self
      simp only [List.all_cons,Bool.and_eq_true] at h
      exact h.2
    · exact safe sec (List.mem_cons_of_mem _ hm)

/-- Converting a list of FFI-free Stack functions to Lab sections yields no
external-call names. -/
theorem progToSection_noFfi {width : Nat} [NeZero width]
    (programs : List (Nat × HolProg width))
    (safe : ∀ row ∈ programs, stackNoFfi row.2 = true) :
    findFfiNames (programs.map progToSectionHOL) = [] := by
  apply findFfiNames_of_noFfi
  intro sec member
  obtain ⟨⟨name,body⟩,hin,rfl⟩ := List.mem_map.mp member
  have h := flatten_noFfi true body name (StackAlloc.nextLab body 2) [] [] (safe _ hin)
  simp only [progToSectionHOL,FlattenCorrect.appListAppendAppend,
    FlattenCorrect.appListAppendList,List.all_append,List.all_cons,List.all_nil,labLineNoFfi,
    Bool.and_true] 
  exact h

/-- Register renaming preserves absence of FFI instructions. -/
theorem stackNames_noFfi {width : Nat} [NeZero width] :
    ∀ (names : Spt Nat) (p : HolProg width),
      stackNoFfi p = true → stackNoFfi (StackNames.progCompHOL names p) = true := by
  intro names p
  induction p using StackNames.progCompHOL.induct <;>
    try simp_all [StackNames.progCompHOL,stackNoFfi]
  rename_i rh _ hd ih2 ih1
  rcases rh with _ | ⟨rp,lr,l1,l2⟩ <;> rcases hd with _ | ⟨hp,h1,h2⟩ <;>
    simp_all [StackNames.progCompHOL,stackNoFfi]

/-- Renamed FFI-free Stack functions emit no Lab external-call names. -/
theorem stackNames_sections_noFfi {width : Nat} [NeZero width]
    (names : Spt Nat) (programs : List (Nat × HolProg width))
    (safe : ∀ row ∈ programs, stackNoFfi row.2 = true) :
    findFfiNames ((StackNames.compileHOL names programs).map progToSectionHOL) = [] := by
  apply progToSection_noFfi
  intro row member
  change row ∈ programs.map (StackNames.progCompEntryHOL names) at member
  obtain ⟨⟨id,p⟩,hin,rfl⟩ := List.mem_map.mp member
  exact stackNames_noFfi names p (safe _ hin)

/-- Raw-call lowering preserves absence of FFI instructions. -/
theorem stackRawcall_noFfi {width : Nat} [NeZero width] :
    ∀ (info : Spt Nat) (p : HolProg width),
      stackNoFfi p = true → stackNoFfi (StackRawCall.comp info p) = true := by
  intro info body
  induction body using StackRawCall.comp.induct with
  | case1 first second ihFirst ihSecond =>
    intro h
    simp only [stackNoFfi, Bool.and_eq_true] at h
    by_cases hs : StackRawCall.compSeq first second info
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) =
        .seq (StackRawCall.comp info first) (StackRawCall.comp info second)
    · simp [StackRawCall.comp,hs,stackNoFfi,ihFirst h.1,ihSecond h.2]
    · obtain ⟨k,dest,rfl,rfl⟩ := StackRawCall.compSeqNeqImp first second
        (.seq (StackRawCall.comp info first) (StackRawCall.comp info second)) info hs
      simp only [StackRawCall.comp,StackRawCall.compSeq,StackRawCall.destCase]
      split <;> try simp_all [stackNoFfi]
      all_goals split <;> try simp_all [stackNoFfi]
      all_goals split <;> try simp_all [stackNoFfi]
  | _ => intro h; simp_all [StackRawCall.comp,stackNoFfi]

/-- The top-level raw-call transformation preserves the same property. -/
theorem stackRawcallTop_noFfi {width : Nat} [NeZero width] (info : Spt Nat)
    (p : HolProg width) (safe : stackNoFfi p = true) :
    stackNoFfi (StackRawCall.compTop info p) = true := by
  rw [StackRawCall.compTop.eq_def]
  split
  · rename_i a b
    simp only [stackNoFfi,Bool.and_eq_true] at safe ⊢
    exact ⟨stackRawcall_noFfi info a safe.1,stackRawcall_noFfi info b safe.2⟩
  · exact stackRawcall_noFfi info _ safe

/-- Stack allocation lowering preserves FFI exclusion in a program body. -/
theorem stackAlloc_noFfi {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width),
      stackNoFfi p = true → stackNoFfi (StackAlloc.comp n m p).1 = true := by
  intro n m p
  set_option tactic.fun_induction.unfolding false in
    fun_induction StackAlloc.comp n m p with
    | _ => simp_all [StackAlloc.comp,stackNoFfi]

theorem upshift_noFfi {width : Nat} [NeZero width] :
    ∀ k n : Nat, stackNoFfi (StackRemove.upshift k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.upshift]
    split
    · simp [stackNoFfi]
    · simp only [stackNoFfi, Bool.true_and]
      apply ih; simp only [StackRemove.maxStackAlloc] at *; omega

theorem downshift_noFfi {width : Nat} [NeZero width] :
    ∀ k n : Nat, stackNoFfi (StackRemove.downshift k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.downshift]
    split
    · simp [stackNoFfi]
    · simp only [stackNoFfi, Bool.true_and]
      apply ih; simp only [StackRemove.maxStackAlloc] at *; omega

theorem stackFree_noFfi {width : Nat} [NeZero width] :
    ∀ k n : Nat, stackNoFfi (StackRemove.stackFree k n : HolProg width) = true := by
  intro k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.stackFree]
    split
    · simp [stackNoFfi]
    split
    · simp [StackRemove.singleStackFree, stackNoFfi]
    · simp only [stackNoFfi, Bool.and_eq_true]
      refine ⟨by simp [StackRemove.singleStackFree, stackNoFfi], ih _ ?_⟩
      simp only [StackRemove.maxStackAlloc] at *; omega

theorem stackAllocInst_noFfi {width : Nat} [NeZero width] :
    ∀ (jump : Bool) (k n : Nat),
      stackNoFfi (StackRemove.stackAlloc jump k n : HolProg width) = true := by
  intro jump k n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [StackRemove.stackAlloc]
    split
    · simp [stackNoFfi]
    split
    · unfold StackRemove.singleStackAlloc; split <;> simp [stackNoFfi, StackRemove.haltInst]
    · simp only [stackNoFfi, Bool.and_eq_true]
      refine ⟨by unfold StackRemove.singleStackAlloc; split <;>
        simp [stackNoFfi, StackRemove.haltInst], ih _ ?_⟩
      simp only [StackRemove.maxStackAlloc] at *; omega

theorem stackRemove_noFfi {width : Nat} [NeZero width] :
    ∀ (jump : Bool) (off : BitVec width × BitVec width) (k : Nat) (p : HolProg width),
      stackNoFfi p = true → stackNoFfi (StackRemove.comp jump off k p) = true := by
  intro jump off k p
  induction p using StackRemove.comp.induct (bounds := off) <;>
    (try simp only [StackRemove.comp]) <;>
    (try split) <;>
    (try simp_all [stackNoFfi, stackAllocInst_noFfi, stackFree_noFfi, upshift_noFfi,
      downshift_noFfi, StackRemove.stackStore, StackRemove.stackLoad, moveInst,
      moveHOL, addInst, subInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.loadInst, StackRemove.storeInst, addBytesInWordInst, listSeqHOL,
      StackRemove.copyLoop, StackRemove.copyEach, whileHOL])
  case case22 ret _ handler ih2 ih1 =>
    rcases ret with _ | ⟨b, r, l1, l2⟩ <;> rcases handler with _ | ⟨h, h1, h2⟩ <;>
      simp_all [StackRemove.comp, stackNoFfi]


theorem wordGc_noFfi {width : Nat} [NeZero width] (c : DataToWord.Config) :
    stackNoFfi (StackAlloc.wordGcCode (width := width) c) = true := by
  unfold StackAlloc.wordGcCode
  split
  · simp [stackNoFfi, listSeqHOL, StackRemove.constInst]
  · simp [stackNoFfi, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, add1Inst, orInst,
      addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
      StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
      StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode,
      StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode,
      StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode]
  · rename_i sizes _
    cases sizes
    · simp [stackNoFfi, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
        orInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
        StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
        StackAlloc.clearTopInst, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcMoveDataCode,
        StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode,
        StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]
    · simp [stackNoFfi, listSeqHOL, whileHOL, moveHOL, sub1Inst, subInst, addInst, andInst, add1Inst,
        orInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
        StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst, StackAlloc.memcpyCode,
        StackAlloc.clearTopInst, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode,
        StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode,
        StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode,
        StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode,
        StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode,
        StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode,
        StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode,
        StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger]

theorem initCode_noFfi {width : Nat} [NeZero width] (gen : Bool) (maxHeap k : Nat) :
    stackNoFfi (StackRemove.initCode (width := width) gen maxHeap k) = true := by
  have hs : ∀ (a t : Nat) (ls : List (BitVec width ⊕ Nat)),
      stackNoFfi (StackRemove.storeListCode a t ls) = true := by
    intro a t ls
    induction ls with
    | nil => simp [StackRemove.storeListCode, stackNoFfi]
    | cons x xs ih =>
      rcases x with v | r <;>
        simp [StackRemove.storeListCode, stackNoFfi, listSeqHOL, addBytesInWordInst, ih]
  simp [StackRemove.initCode, stackNoFfi, listSeqHOL, StackRemove.initMemory, hs, moveHOL,
    subInst, addInst, addBytesInWordInst, StackRemove.leftShiftInst, StackRemove.rightShiftInst,
    StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst]


theorem stackRawcallCompile_noFfi {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, stackNoFfi ap.2 = true) →
      ∀ ap ∈ StackRawCall.compile prog, stackNoFfi ap.2 = true := by
  intro prog h ap hap
  simp only [StackRawCall.compile, List.mem_map] at hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := hap
  exact stackRawcallTop_noFfi _ p (h _ hm)


theorem stackAllocProg_noFfi {width : Nat} [NeZero width] :
    ∀ prog : List (Nat × HolProg width), (∀ ap ∈ prog, stackNoFfi ap.2 = true) →
      ∀ ap ∈ prog.map StackAlloc.progComp, stackNoFfi ap.2 = true := by
  intro prog h ap hap
  obtain ⟨⟨a, p⟩, hm, rfl⟩ := List.mem_map.mp hap
  exact stackAlloc_noFfi a _ p (h _ hm)


theorem stackAllocCompile_noFfi {width : Nat} [NeZero width] {data : DataToWord.Config}
    {prog : List (Nat × HolProg width)} :
    (∀ ap ∈ prog, stackNoFfi ap.2 = true) →
      ∀ ap ∈ StackAlloc.compile data prog, stackNoFfi ap.2 = true := by
  intro h ap hap
  simp only [StackAlloc.compile, StackAlloc.stubs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hap
  rcases hap with rfl | hap
  · simp [stackNoFfi, wordGc_noFfi]
  · exact stackAllocProg_noFfi prog h ap hap


theorem stackRemoveCompile_noFfi {width : Nat} [NeZero width] {jump : Bool}
    {offset : BitVec width × BitVec width} {gckind : Bool} {mh sp loc : Nat}
    {prog : List (Nat × HolProg width)} :
    (∀ ap ∈ prog, stackNoFfi ap.2 = true) →
      ∀ ap ∈ StackRemove.compileHOL jump offset gckind mh sp loc prog, stackNoFfi ap.2 = true := by
  intro h ap hap
  simp only [StackRemove.compileHOL, StackRemove.initStubs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hap
  rcases hap with (rfl | rfl | rfl) | ⟨⟨a, p⟩, hm, rfl⟩
  · simp [stackNoFfi, initCode_noFfi]
  · simp [stackNoFfi, StackRemove.haltInst]
  · simp [stackNoFfi, StackRemove.haltInst]
  · exact stackRemove_noFfi jump offset sp p (h _ hm)



/-- The full Stack-to-Lab compiler emits no external-call names from an
FFI-free input program, including its generated runtime stubs. -/
theorem stackToLab_noFfi {width : Nat} [NeZero width]
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config)
    (maxHeap sp : Nat) (offset : BitVec width × BitVec width)
    (programs : List (Nat × HolProg width))
    (safe : ∀ row ∈ programs, stackNoFfi row.2 = true) :
    findFfiNames (StackToLab.compile stackConf dataConf maxHeap sp offset programs) = [] := by
  unfold StackToLab.compile
  apply stackNames_sections_noFfi
  apply stackRemoveCompile_noFfi
  apply stackAllocCompile_noFfi
  exact stackRawcallCompile_noFfi programs safe

end SteppedFlapjack.LabToTargetSteps
