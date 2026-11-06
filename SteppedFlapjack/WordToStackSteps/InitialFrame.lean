import SteppedFlapjack.WordToStackSteps.WholeInitialization
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail

/-! Enter the first allocated Word function from the zero-frame relation. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

/-- With all entry arguments in registers, allocating the compiler-selected
frame preserves the native Word/Stack relation. The Word call environment
accounts for the frame in its locals size and maximum stack usage. -/
theorem initialFrame_stateRel (ac : AsmConfigExact width) (k frameSize frame : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (t : StackSemStateFiniteExact width C F)
    (args : List (WordLocW width))
    (related : stateRel ac k 0 0 s t [] 0)
    (locals : s.locals = sptFromList2 args) (argBound : args.length ≤ k)
    (frameShape : if frame = 0 then frameSize = 0 else frameSize = frame+1)
    (space : frameSize ≤ t.stackSpace) :
    stateRel ac k frameSize frame (callEnv args (some frameSize) s)
      {t with stackSpace := t.stackSpace-frameSize} [] 0 := by
  unfold stateRel at related
  obtain ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18,
    g19,g20,g21,g22,g23,g24,g25,g26,g27,g28,g29,g30,g31,g32,g33,g34,_,_,resource,oldStack,oldLocals⟩ := related
  unfold stateRel
  refine ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18,
    g19,g20,g21,g22,g23,g24,g25,g26,g27,g28,g29,g30,g31,g32,?_,g34,frameShape,
    wfFromList2 args,?_,?_,?_⟩
  · simp only
    omega
  · change stackSizeRel frameSize (some frameSize) s.stackLimit
      (wordSemOptionMax s.stackMax (wordSemOptionAdd (wordSemStackSize s.stack) (some frameSize)))
      s.stack t.stack (t.stackSpace-frameSize) 0
    obtain ⟨_,limit,maximum⟩ := resource
    refine ⟨fun _ => rfl,limit,?_⟩
    intro newMaximum newValue
    rcases oldValue : s.stackMax with _ | oldMaximum
    · rw [oldValue] at newValue
      simp [wordSemOptionMax] at newValue
    obtain ⟨oldBound,_,stackWords,stackSize,stackValue⟩ := maximum oldMaximum oldValue
    rw [oldValue,stackSize] at newValue
    simp only [wordSemOptionMax,wordSemOptionAdd,Option.some.injEq] at newValue
    have lower := Nat.le_max_right oldMaximum (stackWords+frameSize)
    refine ⟨by omega,by simp,stackWords,stackSize,by omega⟩
  · change stackRel k s.handler s.stack (t.store.lookup .handler)
      (((t.stack.drop (t.stackSpace-frameSize+0)).drop frameSize)) t.stack.length t.bitmaps []
    rw [List.drop_drop,Nat.add_zero,Nat.sub_add_cancel space]
    simpa only [Nat.add_zero,List.drop_zero] using oldStack
  · intro key value lookup
    change sptLookup key (sptFromList2 args) = some value at lookup
    have original : sptLookup key s.locals = some value := by simpa only [locals] using lookup
    obtain ⟨even,located⟩ := oldLocals key value original
    have index : key / 2 < args.length := by
      rw [fromList2Lookup,if_pos even] at lookup
      exact (List.getElem?_eq_some_iff.mp lookup).1
    have phys : key / 2 < k := by omega
    refine ⟨even,?_⟩
    simp only [if_pos phys] at located ⊢
    exact located

/-- The native initial state enters a register-only entry function with its
return location in register zero and the actual allocated frame. -/
theorem wholeWordStack_initialFrame (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : AsmConfigExact width) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst)
    (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2).1.IsPrefix t.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk
      ac (ac.regCount-(5+ac.avoidRegs.length)) t coracle)
    (frameSize frame : Nat) (frameShape : if frame = 0 then frameSize = 0 else frameSize = frame+1)
    (space : frameSize ≤ t.stackSpace) :
    let source := Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit
      ac (ac.regCount-(5+ac.avoidRegs.length)) t
      (sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2) coracle
    stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
      (callEnv [(.loc 1 0 : WordLocW width)] (some frameSize) source)
      {t with stackSpace := t.stackSpace-frameSize} [] 0 := by
  have init := wholeWordStack_initStateRel wc ac programs t coracle noRaise noStore codeEq bitmapsPrefix ok
  have kBound : 1 ≤ ac.regCount-(5+ac.avoidRegs.length) := by
    have h := ok.1
    omega
  apply initialFrame_stateRel ac _ frameSize frame _ t [(.loc 1 0 : WordLocW width)] init
  · simp [Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,sptFromList2]
  · simpa using kBound
  · exact frameShape
  · exact space

end SteppedFlapjack.WordToStackSteps
