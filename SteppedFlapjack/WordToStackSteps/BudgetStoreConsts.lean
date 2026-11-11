import SteppedFlapjack.WordToStackSteps.BudgetSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.StoreConsts
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend.WordToStack.Native
private theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (first second addressRegister offsetRegister : Nat)
    (words : List (Bool × BitVec width))
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate
      (.storeConsts first second addressRegister offsetRegister words) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ address offset : BitVec width,
      WordSemStateFiniteExact.getVar addressRegister source = some (.word address) ∧
      WordSemStateFiniteExact.getVar offsetRegister source = some (.word offset) ∧
      wordSemConstAddresses address words source.mdomain = true ∧
      result = none ∧
      post = WordSemStateFiniteExact.setVar addressRegister
        (.word (address + wordSemBytesInWord * BitVec.ofNat width words.length))
        (WordSemStateFiniteExact.setVar offsetRegister (.word offset)
          (WordSemStateFiniteExact.unsetVar first (WordSemStateFiniteExact.unsetVar second
            {source with memory := wordSemConstWrites address offset words source.memory}))) := by
  cases addressRead : WordSemStateFiniteExact.getVar addressRegister source with
  | none =>
    simp [WordSemStateFiniteExact.evaluate,addressRead] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  | some addressValue =>
    cases addressValue with
    | loc l n =>
      simp [WordSemStateFiniteExact.evaluate,addressRead] at execution
      obtain ⟨rfl,rfl⟩ := execution
      contradiction
    | word address =>
      cases offsetRead : WordSemStateFiniteExact.getVar offsetRegister source with
      | none =>
        simp [WordSemStateFiniteExact.evaluate,addressRead,offsetRead] at execution
        obtain ⟨rfl,rfl⟩ := execution
        contradiction
      | some offsetValue =>
        cases offsetValue with
        | loc l n =>
          simp [WordSemStateFiniteExact.evaluate,addressRead,offsetRead] at execution
          obtain ⟨rfl,rfl⟩ := execution
          contradiction
        | word offset =>
          by_cases addresses : wordSemConstAddresses address words source.mdomain = true
          · simp only [WordSemStateFiniteExact.evaluate,addressRead,offsetRead,addresses,
              not_true_eq_false,↓reduceIte,Prod.mk.injEq] at execution
            obtain ⟨rfl,rfl⟩ := execution
            exact ⟨address,offset,rfl,rfl,addresses,rfl,rfl⟩
          · simp [WordSemStateFiniteExact.evaluate,addressRead,offsetRead,addresses] at execution
            obtain ⟨rfl,rfl⟩ := execution
            contradiction

/-- Flapjack infrastructure naming the complete actual source update; HOL
writes this state inline in the constructor's evaluator equation. -/
private def sourcePost {width : Nat} [NeZero width] {C F : Type}
    (address offset : BitVec width) (words : List (Bool × BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :=
  WordSemStateFiniteExact.setVar 4
    (.word (address + wordSemBytesInWord * BitVec.ofNat width words.length))
    (WordSemStateFiniteExact.setVar 6 (.word offset)
      (WordSemStateFiniteExact.unsetVar 0 (WordSemStateFiniteExact.unsetVar 2
        {source with memory := wordSemConstWrites address offset words source.memory})))

/-- Flapjack infrastructure naming the actual target writes, including its
bitmap-index prelude and allocation-mode register removal. -/
private def targetPost {width : Nat} [NeZero width] {C F : Type}
    (k index : Nat) (address offset : BitVec width) (words : List (Bool × BitVec width))
    (target : StackSemStateFiniteExact width C F) :=
  StackSemStoreConsts.unsetVarZero
    (StackSemStateOps.setVar k (.word 1) (StackSemStateOps.setVar (k+1) (.word 1)
      (StackSemStateOps.setVar 1 (.word 1) (StackSemStateOps.setVar 2
        (.word (address + wordSemBytesInWord * BitVec.ofNat width words.length))
        {StackSemStateOps.setVar 1 (.word (BitVec.ofNat width index)) target with
          memory := wordSemConstWrites address offset words target.memory}))))

/-- Flapjack infrastructure for the original inline StoreConsts postrelation:
all original stateRel conjuncts, not merely memory or register observations. -/
private theorem postRelated {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width) (k f frame index : Nat)
    (address offset : BitVec width) (words : List (Bool × BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (related : stateRel ac k f frame source target lens 0)
    (offsetRead : WordSemStateFiniteExact.getVar 6 source = some (.word offset)) :
    stateRel ac k f frame (sourcePost address offset words source)
      (targetPost k index address offset words target) lens 0 := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩ := related
  refine ⟨h1,h2,h3,h4,h5,h6,h7,?_,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,?_,
    h37,h38,?_⟩
  · exact congrArg (wordSemConstWrites address offset words) h8
  · exact sptWfInsert 4 _ _ (sptWfInsert 6 _ _
      (sptWfDelete _ 0 (sptWfDelete _ 2 h36)))
  · intro n value found
    change sptLookup n (sptInsert 4 _ (sptInsert 6 _
      (sptDelete 0 (sptDelete 2 source.locals)))) = some value at found
    have offsetPlacement := (hloc 6 (.word offset) offsetRead).2
    have offsetPhysical : 6 / 2 < k := by omega
    rw [if_pos offsetPhysical] at offsetPlacement
    by_cases isAddress : n = 4
    · subst n
      rw [sptLookup_sptInsert_same] at found
      have eq := Option.some.inj found
      subst value
      simp [targetPost, StackSemStoreConsts.unsetVarZero, StackSemStateOps.setVar,
        HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL,
        show 2 < k by omega, show 2 ≠ k by omega, show 2 ≠ k+1 by omega]
    · rw [sptLookup_sptInsert_ne 4 n _ _ isAddress] at found
      by_cases isOffset : n = 6
      · subst n
        rw [sptLookup_sptInsert_same] at found
        have eq := Option.some.inj found
        subst value
        simp [targetPost, StackSemStoreConsts.unsetVarZero, StackSemStateOps.setVar,
          HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL,
          show 3 < k by omega, show 3 ≠ k by omega, show 3 ≠ k+1 by omega,
          offsetPlacement]
      · rw [sptLookup_sptInsert_ne 6 n _ _ isOffset, sptLookup_sptDelete,
          sptLookup_sptDelete] at found
        have notZero : n ≠ 0 := by intro equality; simp [equality] at found
        have notTwo : n ≠ 2 := by intro equality; simp [equality] at found
        simp only [notZero,notTwo,↓reduceIte] at found
        obtain ⟨even,placement⟩ := hloc n value found
        refine ⟨even,?_⟩
        by_cases physical : n / 2 < k
        · rw [if_pos physical] at placement ⊢
          have halfZero : n/2 ≠ 0 := by omega
          have halfOne : n/2 ≠ 1 := by omega
          have halfTwo : n/2 ≠ 2 := by omega
          have halfK : n/2 ≠ k := by omega
          have halfNext : n/2 ≠ k+1 := by omega
          simpa [targetPost, StackSemStoreConsts.unsetVarZero, StackSemStateOps.setVar,
            HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL,
            halfZero,halfOne,halfTwo,halfK,halfNext] using placement
        · rw [if_neg physical] at placement ⊢
          exact placement

/-- Flapjack infrastructure for the source proof's bitmap-prefix decomposition.
The original index and prefix guards derive both the actual bitmap slice and
its index; no selected-bitmap or target execution fact is assumed. -/
private theorem insertedBitmapSlice {width : Nat} [NeZero width]
    (bs : AppList (BitVec width)) (n : Nat) (words : List (Bool × BitVec width))
    (bitmaps : List (BitVec width))
    (lengthBound : (appListAppend bs).length ≤ n)
    (indexBound : n - (appListAppend bs).length ≤ bitmaps.length)
    (bitmapPrefix : (appListAppend (AppList.append bs
      (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length)))).IsPrefix
      (bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ xs ys, bitmaps = xs ++ Compiler.Backend.WordToStack.constWordsToBitmapW words words.length ++ ys ∧
      xs.length = n := by
  have flatten : appListAppend (AppList.append bs
      (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length))) =
      appListAppend bs ++ Compiler.Backend.WordToStack.constWordsToBitmapW words words.length := by
    rw [(appListAppend_thm bs (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length))
      (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length)).1]
    simp [appListAppend,appendAux]
  rw [flatten] at bitmapPrefix
  obtain ⟨ys, suffix⟩ := bitmapPrefix
  refine ⟨bitmaps.take (n - (appListAppend bs).length) ++ appListAppend bs, ys, ?_, ?_⟩
  · have split := List.take_append_drop (n - (appListAppend bs).length) bitmaps
    rw [← suffix] at split
    simpa only [List.append_assoc] using split.symm
  · simp only [List.length_append, List.length_take, Nat.min_eq_left indexBound]
    omega

/-- Flapjack infrastructure for the actual target StoreConsts run. All its
operands, stub, domain and bitmap premises are derived from the original
simulation guards by the assembling case theorem. -/
private theorem targetSuccess {width : Nat} [NeZero width] {C F : Type}
    (k index : Nat) (address offset : BitVec width) (words : List (Bool × BitVec width))
    (target : StackSemStateFiniteExact width C F) (xs ys : List (BitVec width))
    (large : 4 < k) (storeEnabled : target.useStore = true)
    (allocEnabled : target.useAlloc = true)
    (stub : sptLookup storeConstsStubLocation target.code = some (storeConstsStubNative k))
    (readAddress : target.regs.lookup 2 = some (.word address))
    (readOffset : target.regs.lookup 3 = some (.word offset))
    (bitmapSlice : target.bitmaps = xs ++
      Compiler.Backend.WordToStack.constWordsToBitmapW words words.length ++ ys)
    (indexEq : xs.length = index) (indexBound : index < 2 ^ width)
    (addresses : wordSemConstAddresses address words target.mdomain = true)
    (dimension : goodDimindex width) :
    StackSemEvaluate.evaluate
      (.seq (.inst (.const 1 (BitVec.ofNat width index)))
        (.storeConsts k (k+1) (some storeConstsStubLocation)), target) =
      (none, targetPost k index address offset words target) := by
  have copy := Compiler.Backend.WordToStack.copyWordsCorrect words xs ys address offset
    (fun key => target.mdomain key = true) target.memory (by simpa using addresses) dimension
  rw [← bitmapSlice,indexEq] at copy
  have distinct : [0,1,2,3,k,k+1].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, not_or, and_true, or_false]
    omega
  have stubGuard : StackSemStoreConstsGuard.checkStoreConstsOpt k (k+1)
      (some storeConstsStubLocation) target.code = true := by
    simp [StackSemStoreConstsGuard.checkStoreConstsOpt,stub,
      StackSemStoreConstsGuard.isStoreConstsStub,storeConstsStubNative]
  have prelude : StackSemEvaluate.evaluate
      (.inst (.const 1 (BitVec.ofNat width index)), target) =
      (none,StackSemStateOps.setVar 1 (.word (BitVec.ofNat width index)) target) := by
    simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp]
  rw [StackSemEvaluate.evaluate_seq,prelude]
  simp only [StackSemControl.fixClock,StackSemStateOps.setVar,Nat.min_self]
  rw [StackSemEvaluate.evaluate_storeConsts]
  simp only [storeEnabled,allocEnabled,not_true_eq_false,false_and,
    stubGuard,↓reduceIte,StackSemStoreConsts.storeConstSem,distinct]
  simp only [StackSemStateOps.getVar,HolFiniteMapExact.updateEq,FUPDATE_HOL,
    show (2 : Nat) ≠ 1 by omega, show (3 : Nat) ≠ 1 by omega,readAddress,readOffset]
  have wordIndex : (BitVec.ofNat width index).toNat = index := by
    simp [Nat.mod_eq_of_lt indexBound]
  simp only [wordIndex,copy,↓reduceIte]
  simp only [targetPost,StackSemStateOps.setVar,StackSemStoreConsts.unsetVarZero,
    storeEnabled,allocEnabled]
  rfl


/-- Constant copying preserves the original compiler relation with no extra clock. -/
theorem storeConsts_zero {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width)
    (first second addressRegister offsetRegister : Nat) (words : List (Bool × BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.storeConsts first second addressRegister offsetRegister words) source := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [postAllocConventionsHOL,Bool.and_eq_true] at conventions
  have callArgs := conventions.2.2
  have registers : first = 0 ∧ second = 2 ∧ addressRegister = 4 ∧ offsetRegister = 6 := by
    simpa only [callArgConventionHOL,Bool.and_eq_true,beq_iff_eq,and_assoc] using callArgs
  obtain ⟨rfl,rfl,rfl,rfl⟩ := registers
  obtain ⟨address,offset,addressRead,offsetRead,addresses,rfl,postEq⟩ :=
    sourceSuccess 0 2 4 6 words source post result execution notError
  have facts : target.useStore = true ∧ target.useAlloc = true ∧ 4 < k ∧
      sptLookup storeConstsStubLocation target.code = some (storeConstsStubNative k) ∧
      goodDimindex width ∧ target.mdomain = source.mdomain ∧
      target.bitmaps.length < 2 ^ width ∧
      target.regs.lookup 2 = some (.word address) ∧ target.regs.lookup 3 = some (.word offset) := by
    unfold stateRel at related
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
      h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
      h37,h38,hloc⟩ := related
    refine ⟨h6,h7,h10,h27,h28,h9,by omega,?_,?_⟩
    · have value := (hloc 4 (.word address) addressRead).2
      simpa only [show 4/2 < k by omega,if_true] using value
    · have value := (hloc 6 (.word offset) offsetRead).2
      simpa only [show 6/2 < k by omega,if_true] using value
  obtain ⟨storeEnabled,allocEnabled,large,stub,dimension,domains,bitmapLength,
    targetAddress,targetOffset⟩ := facts
  have compiledEq : compiled = Compiler.Backend.StackLang.Prog.seq
      (.inst (.const 1 (BitVec.ofNat width n)))
      (.storeConsts k (k+1) (some storeConstsStubLocation)) := by
    have equality := congrArg Prod.fst compilation
    simpa only [compNative,Compiler.Backend.WordToStack.insertBitmap] using equality.symm
  have outputEq : bsPost = AppList.append bs
      (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length)) := by
    have equality := congrArg (fun output => output.2.1) compilation
    simpa only [compNative,Compiler.Backend.WordToStack.insertBitmap] using equality.symm
  subst compiled
  subst bsPost
  obtain ⟨xs,ys,bitmapSlice,indexEq⟩ :=
    insertedBitmapSlice bs n words target.bitmaps lengthBound bitmapBound bitmapPrefix
  have indexBound : n < 2 ^ width := by
    rw [bitmapSlice] at bitmapLength
    simp only [List.length_append] at bitmapLength
    omega
  have targetAddresses : wordSemConstAddresses address words target.mdomain = true := by
    rw [domains]
    exact addresses
  subst post
  refine ⟨targetPost k n address offset words target,none,?_,?_⟩
  · simpa only [Nat.add_zero] using targetSuccess k n address offset words target xs ys
      large storeEnabled allocEnabled stub targetAddress targetOffset bitmapSlice indexEq
      indexBound targetAddresses dimension
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte,sourcePost] using
      postRelated ac k f frame n address offset words source target lens related offsetRead

end SteppedFlapjack.WordToStackSteps
