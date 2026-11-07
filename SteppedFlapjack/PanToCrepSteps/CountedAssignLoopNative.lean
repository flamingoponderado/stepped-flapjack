import SteppedFlapjack.PanToCrepSteps.AssignLoopEntryDefs
import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopReturn
import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations
import SteppedFlapjack.CrepToLoopSteps.RiscVInputs
import SteppedFlapjack.LoopToWordSteps.TailRiscVSetup
import SteppedFlapjack.WordToStackSteps.TailEntryFrame
import SteppedFlapjack.PanToCrepSteps.GlobalSourceEntry
import SteppedFlapjack.LoopToWordSteps.TailRiscVClock
import SteppedFlapjack.CrepToLoopSteps.WholeInitialRelations
import SteppedFlapjack.LoopToWordSteps.NativeTailCompilerFacts
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.WordToStackSteps.DirectTailRiscV
import SteppedFlapjack.WordAllocSteps.WholeTailCode
import Flapjack.Pancake.LoopToWord.Proofs.LabPres
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas
import SteppedFlapjack.PanToCrepSteps.GlobalTailWord
import SteppedFlapjack.PanToCrepSteps.GlobalPanCodeRel

/-! Native initialization for the counted assignment-loop entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Whole-compiler and native-machine inputs for a zero-argument Loop entry.
The frame, Word state, code relations, and resource outcome are derived. -/
structure AssignLoopCompilerInputs {F : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (loop : LoopSemStateFiniteExact 64 F) where
  arch : AsmArchitecture
  crepPrograms : List (MlString × List Nat × CrepProgHOL 64)
  programsEq : crepPrograms = compileProgDeclsHOLW (compileTopExactHOL declarations start)
  callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
    (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
  loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable crepPrograms) 0
  wc : Flapjack.Compiler.Backend.WordToWord.Config
  ac : AsmConfigExact 64
  loopCode : loop.code = sptFromAList (compileProgHOLExact arch crepPrograms)
  stack : StackSemStateFiniteExact 64 LabToTarget.Config F
  coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64))
  codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
    (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2
  bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
    (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).1.IsPrefix stack.bitmaps
  ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) stack coracle
  data : LoopWordDataRel loop
    {callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
        (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2) coracle)
      with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))}

/-- Derive the source/Crep/Loop code relations and selected Word entry once
for any supported source main body. -/
theorem AssignLoopCompilerInputs.frontendFacts {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (pan : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ)
    (native : AssignLoopCompilerInputs declarations start caller loopCtxt entry limit target)
    (entryDef : entry = assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
    (original : ProgHOL 64) (returnShape : ShapeHOL)
    (globalFound : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL 64))
    (globalCompiled : globalLoweredDecs declarations start = (initializers,funs,exns,globals))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ e ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL e.2.2.1 = true)
    (preShapes : ∀ n ps p, (n,ps,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) → SupportedCodeBody p)
    (noTail : ∀ n ps init callee, (n,ps,.seq init (.call none callee [])) ∈
      compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (initShape : BranchProgram caller (nestedSeqHOL initializers)) :
    codeRelExactHOLW caller pan.code crep.code ∧
    (∀ n ps body, (n,ps,body) ∈ native.crepPrograms → SupportedCodeBody body) ∧
    crepToLoopCodeRelExact loopCtxt crep.code target.code ∧
    (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms) := by
  obtain ⟨panCodeRelCanonical,programShapesCanonical⟩ := global_supported_panCrep_codeAndShapes
    declarations start pan crep panCode crepCode unique localised preShapes noTail
  have panCodeRel : codeRelExactHOLW caller pan.code crep.code := by
    simpa only [native.callerEq] using panCodeRelCanonical
  have programShapes : ∀ n ps body, (n,ps,body) ∈ native.crepPrograms → SupportedCodeBody body := by
    simpa only [native.programsEq] using programShapesCanonical
  obtain ⟨preInitializers,preRest,preEntry⟩ := globalEntry_preInline declarations start
    original returnShape globalFound
  have preMember : (start,[],.seq (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL preInitializers))
      (.call none (newMainNameHOL declarations) [])) ∈
      compileToCrepExactHOLW (compileTopExactHOL declarations start) := by
    rw [preEntry]
    simp
  have notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst :=
    noTail start [] _ (newMainNameHOL declarations) preMember
  have compiledInitShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)) := by
    rw [← native.callerEq]
    exact branch_compile initShape
  have actualLookup := globalEntry_nonInline_crep_lookup declarations start initializers returnShape original globalFound funs exns globals (by simpa [globalLoweredDecs] using globalCompiled)
    compiledInitShape notInline crep
  have nativeLookup : holAlookup native.crepPrograms start = some ([],
      .seq (compileProgExactHOLW caller (nestedSeqHOL initializers)) (.call none (newMainNameHOL declarations) [])) := by
    simpa only [native.programsEq,native.callerEq] using actualLookup
  have nativeUnique : (native.crepPrograms.map Prod.fst).Nodup := by
    simpa only [native.programsEq] using unique
  have compiledCodeRel := wholeCrep_supported_executable_codeRel native.arch native.crepPrograms start
    (.seq (compileProgExactHOLW caller (nestedSeqHOL initializers)) (.call none (newMainNameHOL declarations) []))
    nativeUnique nativeLookup programShapes
  have codeRel : crepToLoopCodeRelExact loopCtxt crep.code target.code := by
    simpa only [native.loopContextEq,crepCode,← native.programsEq,native.loopCode] using compiledCodeRel
  have actualMember := globalEntry_nonInline_word_member native.arch declarations start initializers returnShape original globalFound funs exns globals (by simpa [globalLoweredDecs] using globalCompiled)
    compiledInitShape notInline crep
  have entryMember : (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms) := by
    simpa [entryDef,assignLoopEntryProgram,assignLoopEntryWordContext,native.programsEq,native.loopContextEq,native.callerEq,
      compFuncHOLExact,listToNumSetHOLExact] using actualMember
  exact ⟨panCodeRel,programShapes,codeRel,entryMember⟩

end SteppedFlapjack.PanToCrepSteps
