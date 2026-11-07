import SteppedFlapjack.WordToStackSteps.WholeProgram

/-! Function-name properties of the actual native Stack code table. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Native compilation preserves function keys after prepending its two
runtime stubs. -/
theorem compileNative_code_keys {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    (compileNative ac false programs).2.2.2.map Prod.fst =
      raiseStubLocation :: storeConstsStubLocation :: programs.map Prod.fst := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let initial : AppList (BitVec width) × Nat := (.list [4],1)
  rcases compiled : compileWordToStackNative ac false k programs initial with ⟨bodies,frames,bitmaps⟩
  have keys := Flapjack.WordToStackProofs.mapFstCompileWordToStack ac false k programs initial bodies
    (frames,bitmaps) compiled
  change raiseStubLocation :: storeConstsStubLocation ::
    (compileWordToStackNative ac false k programs initial).1.map Prod.fst = _
  rw [compiled]
  rw [keys]

/-- With distinct source functions and no collision with the runtime stubs,
the actual native Stack code has distinct function names. -/
theorem compileNative_code_nodup {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (nodup : (programs.map Prod.fst).Nodup)
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst)
    (noStore : storeConstsStubLocation ∉ programs.map Prod.fst) :
    ((compileNative ac false programs).2.2.2.map Prod.fst).Nodup := by
  rw [compileNative_code_keys]
  simp only [List.nodup_cons,List.mem_cons,not_or]
  exact ⟨⟨by decide,noRaise⟩,noStore,nodup⟩

end SteppedFlapjack.WordToStackSteps
