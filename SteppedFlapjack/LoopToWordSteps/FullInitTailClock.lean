import SteppedFlapjack.LoopToWordSteps.FullInitTailSetup

/-! Clock shifts preserve full-initialization setup witnesses. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.Compiler.Backend

/-- The setup depends on the input Word clock only after replacing it by the
compiler's replay clock, so its witnesses apply at any input Word clock. -/
def FullInitTailSetup.withWordClock {F : Type} {p : HolLoopProg 64}
    {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {limit : Nat}
    (setup : FullInitTailSetup p word limit) (clock : Nat) :
    FullInitTailSetup p {word with clock := clock} limit :=
  { setup with
    gc := by simpa using setup.gc
    noInstall := by simpa using setup.noInstall
    codeRel := by simpa using setup.codeRel
    codeDomain := by simpa using setup.codeDomain
    localsRel := by simpa using setup.localsRel
    stackRel := by simpa using setup.stackRel }

/-- Changing the source Word clock does not change the machine tick bound. -/
theorem FullInitTailSetup.withWordClock_tickLimit {F : Type} {p : HolLoopProg 64}
    {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {limit : Nat}
    (setup : FullInitTailSetup p word limit) (clock : Nat) :
    (setup.withWordClock clock).tickLimit = setup.tickLimit := rfl

/-- Stack safety is unchanged because the replay replaces the Word clock. -/
theorem FullInitTailSetup.withWordClock_wordSafe {F : Type} {p : HolLoopProg 64}
    {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {limit : Nat}
    (setup : FullInitTailSetup p word limit) (clock : Nat) :
    (setup.withWordClock clock).wordSafe ↔ setup.wordSafe := Iff.rfl

end SteppedFlapjack.LoopToWordSteps
