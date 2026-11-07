import SteppedFlapjack.PanToCrepSteps.CountdownZeroFrontendSafe
import SteppedFlapjack.PanToCrepSteps.FullInitAssignLoopInputs

/-! Carry concrete Word stack safety into the source-return machine bound. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- The actual optimized Word program of the zero-count source. -/
noncomputable def countdownZeroWordProgram : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  (compile countdownRiscVBackend.wordToWordConf riscvConfig
    (panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64))))))))).2

/-- The compiler-input fields for the concrete source select exactly the
zero-count Word program used by the machine-safety proof. -/
theorem FullInitAssignLoopInputs.countdownZero_wordProgram {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (target : LoopSemStateFiniteExact 64 σ)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt entry limit target)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))
    (startEq : start = ofString "main") (archEq : native.arch = riscvConfig.isa)
    (wcEq : native.wc = countdownRiscVBackend.wordToWordConf) :
    (compile native.wc riscvConfig (loopToWordCompileHOL
      (compileProgHOLExact native.arch native.crepPrograms))).2 = countdownZeroWordProgram := by
  rw [native.programsEq,archEq,wcEq,declarationsEq,startEq]
  unfold countdownZeroWordProgram
  rw [singleEntry_countdown_panToWord riscvConfig.isa (ofString "x") (0 : BitVec 64) (0 : BitVec 64)]

/-- When the compiler inputs are the actual zero-count optimized Word code,
the source return has a successful machine outcome within the fitting-frame
bound. No resource-limit outcome is needed. -/
theorem FullInitAssignLoopInputs.countdownZero_machineBound_safe {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (target : LoopSemStateFiniteExact 64 σ)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt entry limit target)
    (programShapes : ∀ n ps body, (n,ps,body) ∈ native.crepPrograms → SupportedCodeBody body)
    (entryMember : (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
    (sourceFinal : PanSemStateFiniteExact 64 σ)
    (ready : ∀ word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) σ,
      loopToWordStateRelHOLExact {target with locals := .ln} word →
      ∃ extra, FullInitReturnedReady entry {target with locals := .ln, clock := target.clock+extra}
        {word with clock := word.clock+extra} limit sourceFinal)
    (acEq : native.ac = riscvConfig)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))
    (startEq : start = ofString "main") (archEq : native.arch = riscvConfig.isa)
    (wcEq : native.wc = countdownRiscVBackend.wordToWordConf) :
    ∃ ticks finalMachine finalFfi,
      ticks ≤ native.backend.successTickLimit native.wc riscvConfig
        (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let initial := {target with locals := .ln}
  have wordProgram := native.countdownZero_wordProgram declarations start caller loopCtxt entry limit target
    declarationsEq startEq archEq wcEq
  have wordCode : sptFromAList (compile native.wc riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))).2 = countdownZeroWordCode := by
    rw [wordProgram]
    rfl
  let entryBody : HolProg 64 := .seq .skip (.seq .skip (.call none (.inl 65) none))
  have zeroEntry : sptLookup firstLoopName native.stack.code = some (.seq (.stackAlloc 0) entryBody) := by
    rw [native.codeEq,acEq,wordProgram]
    unfold countdownZeroWordProgram entryBody
    rw [← WordToWord.compileWith_eq_compile Flapjack.RegAlloc.regAllocExecutable (by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g)]
    exact countdownZero_native_entry_exact
  have enabled : native.stack.useStack = true := native.ok.2.2.2.1
  have data : LoopWordDataRel initial {countdownZeroInitialWord native.stack native.coracle with
      code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))} := by
    simpa only [initial,LoopWordDataRel,acEq,wordCode,countdownZeroInitialWord,countdownZeroLimit] using native.data
  obtain ⟨word,setup,contextEq,machineEq,mcEq,labEq,tickEq,wordRel,safe,base,wordLocals⟩ :=
    countdownZero_wholeFrontend_safe native.arch native.crepPrograms programShapes native.wc entry
      (assignLoopEntryWordContext entry) (firstLoopName,2) entryMember initial
      (by simpa [initial] using native.loopCode) native.stack native.coracle
      (by simpa only [acEq] using native.codeEq) (by simpa only [acEq] using native.bitmapsPrefix)
      (by simpa only [acEq,countdownZeroLimit] using native.ok) limit data native.backend entryBody zeroEntry enabled wordCode
  obtain ⟨extra,nativeReady⟩ := ready word wordRel
  obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,success,events⟩ :=
    FullInitReturnedReady.run_shifted_safe (loop := initial) (sourceFinal := sourceFinal) extra nativeReady setup base 0
      (by rfl) (by simpa [assignLoopEntryWordContext] using contextEq) wordLocals safe
  subst outcome
  refine ⟨ticks,finalMachine,finalFfi,?_,?_,events⟩
  · simpa only [tickEq] using bound
  · simpa only [mcEq,labEq,machineEq] using run

end SteppedFlapjack.PanToCrepSteps
