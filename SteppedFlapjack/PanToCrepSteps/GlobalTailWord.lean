import SteppedFlapjack.PanToCrepSteps.GlobalCrepEntry
import SteppedFlapjack.CrepToLoopSteps.SimpFixed
import SteppedFlapjack.WordAllocSteps.WholeTailCode
import SteppedFlapjack.WordToStackSteps.WholeTailInitialization
import SteppedFlapjack.WordToStackSteps.TailEntryFrame
import SteppedFlapjack.StackAllocSteps.NamedPipelineClock
import SteppedFlapjack.CrepToLoopSteps.WholeInitialRelations
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames
import Flapjack.Pancake.LoopToWord.Proofs.LabPres
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas

/-! The real global wrapper reaches the actual whole-program Word input. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.StackToLabSteps SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs.InitializationStateRel Flapjack.WordSemStateFiniteExact


/-- The actual Crep simplifier leaves a supported initializer and direct
zero-argument tail call unchanged. -/
theorem branchTail_simp_fixed {width : Nat} [NeZero width] (init : CrepProgHOL width)
    (shape : CrepToLoopSteps.BranchProgram init) (name : MlString) :
    crepSimpProgHOL (.seq init (.call none name [])) = .seq init (.call none name []) := by
  simp [crepSimpProgHOL,branchProgram_simp_fixed shape]

/-- A supported tail wrapper at a known Crep list position occurs at its exact
compiler-generated Word location, after simplification and Loop optimization. -/
theorem tailEntry_crepToWord_member_at {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (code : List (MlString × List Nat × CrepProgHOL width))
    (index : Nat) (hi : index < code.length) (name callee : MlString)
    (init : CrepProgHOL width) (shape : CrepToLoopSteps.BranchProgram init)
    (entry : code[index] = (name,[],.seq init (.call none callee []))) :
    let loop := optimiseHOL (compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable code) []
      (.seq init (.call none callee [])))
    let location := index + firstLoopName
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
    (location,1,(LoopToWord.compHOL ctxt loop (location,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact arch code) := by
  have fixed := branchTail_simp_fixed init shape callee
  have member : (index+firstLoopName,[],
      optimiseHOL (compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable code) []
        (.seq init (.call none callee [])))) ∈ compileProgHOLExact arch code := by
    apply List.mem_iff_getElem.mpr
    refine ⟨index,?_,?_⟩
    · simp only [compileProgHOLExact,List.length_zipWith,List.length_map,List.length_range,Nat.min_self]
      exact hi
    · simp only [compileProgHOLExact,List.getElem_zipWith,List.getElem_map,List.getElem_range,entry,fixed]
      rfl
  exact LoopLiveSteps.loopToWord_zeroArg_member _ _ _ member

/-- The global wrapper preserved by the real inliner is the actual first
Word entry, with the precise optimized Loop body used by the step theorem. -/
theorem globalEntry_nonInline_word_member {width : Nat} [NeZero width] {F : Type}
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (declarations : List (DeclHOL width)) (start : MlString)
    (initializers : List (ProgHOL width)) (returnShape : ShapeHOL) (original : ProgHOL width)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL width)) (context : PanGlobalsContextExact width)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (initShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)))
    (notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (state : CrepSemHOLState width F) :
    let lowered := compileTopExactHOL declarations start
    let sourceContext : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
    let code := compileProgDeclsHOLW lowered
    let loop := optimiseHOL (compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable code) []
      (.seq init (.call none (newMainNameHOL declarations) [])))
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
    (firstLoopName,1,(LoopToWord.compHOL ctxt loop (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact arch code) := by
  obtain ⟨bound,entry,_⟩ := globalEntry_nonInline_preserved declarations start initializers returnShape original found
    funs exns context compiled initShape notInline state
  have member := tailEntry_crepToWord_member_at arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))
    0 bound start (newMainNameHOL declarations) _ initShape entry
  simpa only [Nat.zero_add] using member

/-- The actual global entry is found in both the Word input and whole-compiler output tables. -/
theorem globalEntry_nonInline_wholeWord_lookups {width : Nat} [NeZero width] {F : Type}
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (declarations : List (DeclHOL width)) (start : MlString)
    (initializers : List (ProgHOL width)) (returnShape : ShapeHOL) (original : ProgHOL width)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL width)) (context : PanGlobalsContextExact width)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (initShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)))
    (notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (state : CrepSemHOLState width F)
    (wc : Compiler.Backend.WordToWord.Config) (ac : Compiler.Encoders.Asm.AsmConfigExact width) :
    let lowered := compileTopExactHOL declarations start
    let sourceContext : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
    let code := compileProgDeclsHOLW lowered
    let loopContext := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable code) 0
    let loop := optimiseHOL (compileHOLExact loopContext .ln (.seq init (.call none (newMainNameHOL declarations) [])))
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
    let programs := loopToWordCompileHOL (compileProgHOLExact arch code)
    let q := (LoopToWord.compHOL ctxt loop (firstLoopName,2)).1
    let out := (Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((firstLoopName,1,q),SteppedFlapjack.WordAllocSteps.entryColour wc programs firstLoopName)).2.2
    sptLookup firstLoopName (sptFromAList programs) = some (1,q) ∧
    sptLookup firstLoopName (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) = some (1,out) := by
  have member := globalEntry_nonInline_word_member arch declarations start initializers returnShape original found
    funs exns context compiled initShape notInline state
  have exactMember : (firstLoopName,1,(LoopToWord.compHOL
      (makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL
        (optimiseHOL (compileHOLExact (mkCtxtExact arch (makeVmapExact [])
          (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0) .ln
          (.seq (compileProgExactHOLW (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
            (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
            (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers))
            (.call none (newMainNameHOL declarations) [])))) .ln) (toNumSetHOL []))) .ln)
      (optimiseHOL (compileHOLExact (mkCtxtExact arch (makeVmapExact [])
        (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0) .ln
        (.seq (compileProgExactHOLW (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
          (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
          (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers))
          (.call none (newMainNameHOL declarations) [])))) (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))) := by
    simpa [compFuncHOLExact,listToNumSetHOLExact] using member
  have unique : ((loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))).map Prod.fst).Nodup :=
    loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact arch _)
  exact SteppedFlapjack.WordAllocSteps.wholeCompile_entry_lookups wc ac _ firstLoopName 1 _ exactMember unique

/-- Native Stack initialization witnesses for the actual global wrapper. -/
theorem globalEntry_nonInline_stack_inputs {width : Nat} [NeZero width] {C F : Type}
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (declarations : List (DeclHOL width)) (start : MlString)
    (initializers : List (ProgHOL width)) (returnShape : ShapeHOL) (original : ProgHOL width)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL width)) (context : PanGlobalsContextExact width)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact width :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (initShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)))
    (notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (state : CrepSemHOLState width F)
    (wc : Compiler.Backend.WordToWord.Config) (ac : Compiler.Encoders.Asm.AsmConfigExact width)
    (stack : StackSemStateFiniteExact width C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) :
    let lowered := compileTopExactHOL declarations start
    let sourceContext : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
    let code := compileProgDeclsHOLW lowered
    let loopContext := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable code) 0
    let loop := optimiseHOL (compileHOLExact loopContext .ln (.seq init (.call none (newMainNameHOL declarations) [])))
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
    let programs := loopToWordCompileHOL (compileProgHOLExact arch code)
    let q := (LoopToWord.compHOL ctxt loop (firstLoopName,2)).1
    let out := (Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((firstLoopName,1,q),SteppedFlapjack.WordAllocSteps.entryColour wc programs firstLoopName)).2.2
    Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) 0 0
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length))
        stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle :
          WordSemStateFiniteExact width (Nat × C) F) stack [] 0 ∧
    ∃ bs n bsPost nPost body frame frameSize,
      SteppedFlapjack.WordToStackSteps.nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length))
        firstLoopName (Compiler.Backend.WordToWord.compile wc ac programs).2 (.list [4],1) = some (bs,n) ∧
      frame = max (maxVarHOL out / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (1-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false out (bs,n)
        (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup firstLoopName stack.code = some (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative
        ac false out 1 (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ stack.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (stack.bitmaps.drop (n-(appListAppend bs).length)) := by
  have lookups := globalEntry_nonInline_wholeWord_lookups arch declarations start initializers returnShape original found
    funs exns context compiled initShape notInline state wc ac
  have lookup := lookups.1
  rw [sptLookup_sptFromAList] at lookup
  have member := Flapjack.sptAListLookup_mem _ _ _ lookup
  have unique : ((loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))).map Prod.fst).Nodup :=
    loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact arch _)
  have minimum : ∀ entry ∈ loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))), 60 ≤ entry.1 := by
    apply LoopToWord.loop_to_word_compile_lab_min _ _ 60
    exact ⟨rfl,crep_to_loop_compile_prog_lab_min arch _ _ rfl⟩
  have noRaise : raiseStubLocation ∉ (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))).map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [raiseStubLocation,wordNumStubs,stackNumStubs] at lower
  have noStore : storeConstsStubLocation ∉ (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))).map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [storeConstsStubLocation,wordNumStubs,stackNumStubs] at lower
  exact SteppedFlapjack.WordToStackSteps.wholeWordStack_tail_initialized_inputs wc ac _ firstLoopName 1 _ member unique
    stack coracle noRaise noStore codeEq bitmapsPrefix ok

/-- The actual global entry starts with an initialized frame or reaches the Stack resource limit. -/
theorem globalEntry_nonInline_frame_or_resource {C F : Type}
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (declarations : List (DeclHOL 64)) (start : MlString)
    (initializers : List (ProgHOL 64)) (returnShape : ShapeHOL) (original : ProgHOL 64)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL 64)) (context : PanGlobalsContextExact 64)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact 64 :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (initShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)))
    (notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (state : CrepSemHOLState 64 F)
    (wc : Compiler.Backend.WordToWord.Config) (ac : Compiler.Encoders.Asm.AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) (limit : Nat) :
    let lowered := compileTopExactHOL declarations start
    let sourceContext : PanToCrepContextExact 64 := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
    let code := compileProgDeclsHOLW lowered
    let loopContext := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable code) 0
    let loop := optimiseHOL (compileHOLExact loopContext .ln (.seq init (.call none (newMainNameHOL declarations) [])))
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
    let programs := loopToWordCompileHOL (compileProgHOLExact arch code)
    let q := (LoopToWord.compHOL ctxt loop (firstLoopName,2)).1
    let out := (Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((firstLoopName,1,q),SteppedFlapjack.WordAllocSteps.entryColour wc programs firstLoopName)).2.2
    ∃ bs n bsPost nPost body frame frameSize,
      SteppedFlapjack.WordToStackSteps.nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length))
        firstLoopName (Compiler.Backend.WordToWord.compile wc ac programs).2 (.list [4],1) = some (bs,n) ∧
      frame = max (maxVarHOL out / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (1-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      Compiler.Backend.WordToStack.Native.compNative ac false out (bs,n) (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup firstLoopName stack.code = some (Compiler.Backend.WordToStack.Native.compileProgNative ac false out 1 (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ stack.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (stack.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (frameSize ≤ stack.stackSpace ∧
       Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        (WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle))
        {stack with stackSpace := stack.stackSpace-frameSize} [] 0 ∧
       Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        {(WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle)) with clock := limit}
        {stack with stackSpace := stack.stackSpace-frameSize,clock := limit} [] 0 ∨
       ∃ post, StackSemEvaluate.evaluate (.call none (.inl firstLoopName) none,{stack with clock := limit+1}) =
            (some (.halt (.word 2)),post) ∧ post.ffi = stack.ffi ∧
          StackSteps.steps (.call none (.inl firstLoopName) none,{stack with clock := limit+1}) ≤ 3) := by
  have lookups := globalEntry_nonInline_wholeWord_lookups arch declarations start initializers returnShape original found
    funs exns context compiled initShape notInline state wc ac
  have lookup := lookups.1
  rw [sptLookup_sptFromAList] at lookup
  have member := Flapjack.sptAListLookup_mem _ _ _ lookup
  have unique : ((loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))).map Prod.fst).Nodup :=
    loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact arch _)
  have minimum : ∀ entry ∈ loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))), 60 ≤ entry.1 := by
    apply LoopToWord.loop_to_word_compile_lab_min _ _ 60
    exact ⟨rfl,crep_to_loop_compile_prog_lab_min arch _ _ rfl⟩
  have noRaise : raiseStubLocation ∉ (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))).map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [raiseStubLocation,wordNumStubs,stackNumStubs] at lower
  have noStore : storeConstsStubLocation ∉ (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))).map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [storeConstsStubLocation,wordNumStubs,stackNumStubs] at lower
  exact SteppedFlapjack.WordToStackSteps.wholeWordStack_tailEntryFrame_or_resource wc ac _ firstLoopName _ member unique
    stack coracle noRaise noStore codeEq bitmapsPrefix ok limit

/-- The actual global entry obtains its frame or reaches a bounded RISC-V resource outcome. -/
theorem globalEntry_nonInline_frame_or_riscvResource {F : Type}
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (declarations : List (DeclHOL 64)) (start : MlString)
    (initializers : List (ProgHOL 64)) (returnShape : ShapeHOL) (original : ProgHOL 64)
    (found : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL 64)) (context : PanGlobalsContextExact 64)
    (compiled :
      let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact 64 :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,context))
    (initShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)))
    (notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (state : CrepSemHOLState 64 F)
    (wc : Compiler.Backend.WordToWord.Config) (ac : Compiler.Encoders.Asm.AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) (limit initialClock : Nat)
    (inputCode : List (Nat × HolProg 64))
    (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F) (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : stack.code = sptFromAList inputCode)
    (pre : Pre cr c {stack with code := sptFromAList (StackRawCall.compile inputCode), clock := initialClock} stack.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode), clock := initialClock} 0 stack.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc firstLoopName 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    let lowered := compileTopExactHOL declarations start
    let sourceContext : PanToCrepContextExact 64 := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
    let code := compileProgDeclsHOLW lowered
    let loopContext := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable code) 0
    let loop := optimiseHOL (compileHOLExact loopContext .ln (.seq init (.call none (newMainNameHOL declarations) [])))
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
    let programs := loopToWordCompileHOL (compileProgHOLExact arch code)
    let q := (LoopToWord.compHOL ctxt loop (firstLoopName,2)).1
    let out := (Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((firstLoopName,1,q),SteppedFlapjack.WordAllocSteps.entryColour wc programs firstLoopName)).2.2
    ∃ bs n bsPost nPost body frame frameSize,
      SteppedFlapjack.WordToStackSteps.nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length))
        firstLoopName (Compiler.Backend.WordToWord.compile wc ac programs).2 (.list [4],1) = some (bs,n) ∧
      frame = max (maxVarHOL out / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (1-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      Compiler.Backend.WordToStack.Native.compNative ac false out (bs,n) (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup firstLoopName stack.code = some (Compiler.Backend.WordToStack.Native.compileProgNative ac false out 1 (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ stack.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (stack.bitmaps.drop (n-(appListAppend bs).length)) ∧
      maxVarHOL out < 2*frame+2*(ac.regCount-(5+ac.avoidRegs.length)) ∧
      (∀ loc, StackSem.getLabelsExact body loc → StackSem.locCheckExact stack.code loc) ∧
      (frameSize ≤ stack.stackSpace ∧
       Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        (WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle))
        {stack with stackSpace := stack.stackSpace-frameSize} [] 0 ∧
       Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        {(WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle)) with clock := limit}
        {stack with stackSpace := stack.stackSpace-frameSize,clock := limit} [] 0 ∧
       (∀ temp replayClock,
         let sourceWord := {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
           (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length))
             stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle) with
               code := sptFromAList programs}
         (∀ loopState : LoopSemStateFiniteExact 64 F,
           CrepToLoopSteps.LoopWordDataRel loopState sourceWord ↔
           CrepToLoopSteps.LoopWordDataRel loopState
             {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
               (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length))
                 stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle) with
                   code := sptFromAList programs}) ∧
         Flapjack.Compiler.Backend.WordSimp.gcFunConstOk sourceWord.gcFun ∧
         sptDomain sourceWord.locals = (fun key => key ∈ Flapjack.Compiler.Backend.WordAlloc.evenList 1) ∧
         wordLocalsRel temp sourceWord.locals sourceWord.locals ∧
         sptLookup 0 sourceWord.locals = some (.loc 1 0) ∧
         Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
           {sourceWord with code := (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2), locals := sourceWord.locals, clock := replayClock}
           {stack with stackSpace := stack.stackSpace-frameSize,clock := replayClock} [] 0 ∧
         LoopToWord.localsRelHOL ctxt .ln sourceWord.locals ∧
         ∀ k, sptMem k (accVarsHOL loop .ln) → sptMem k ctxt) ∨
       ∃ (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F),
         ticks ≤ labTickBound 4 labCode lab.codeBuffer *
          (flattenStepFactor * (computedRunCost bounds (uniformFactor (width := 64) c * 3)
            (.call none (.inl firstLoopName) none)
            (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 stack.regs) *
            (uniformFactor (width := 64) c * 3) + 4)) ∧
         evaluateTargetHOL mc lab.ffi ticks machine = (.halt HolOutcome.resourceLimitHit,finalMachine,finalFfi) ∧
         finalFfi.ioEvents = stack.ffi.ioEvents) := by
  obtain ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,compilation,foundEntry,
    lengthBound,gapBound,bitmapPrefix,caseResult⟩ :=
    globalEntry_nonInline_frame_or_resource arch declarations start initializers returnShape original found
      funs exns context compiled initShape notInline state wc ac stack coracle codeEq bitmapsPrefix ok limit
  have entryFacts := SteppedFlapjack.WordToStackSteps.nativeEntry_frame_and_labels ac
    (ac.regCount-(5+ac.avoidRegs.length)) frame frameSize 1 firstLoopName _ stack bs bsPost n nPost body
    frameDef sizeDef compilation foundEntry
  refine ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,compilation,foundEntry,
    lengthBound,gapBound,bitmapPrefix,entryFacts.1,entryFacts.2,?_⟩
  rcases caseResult with success | ⟨post,run,ffi,stepBound⟩
  · left
    refine ⟨success.1,success.2.1,success.2.2,?_⟩
    intro temp replayClock
    have facts := SteppedFlapjack.WordToStackSteps.initializedTail_simulation_state ac _ frameSize frame stack
      (sptFromAList (Compiler.Backend.WordToWord.compile wc ac
        (loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2)
      (sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))) coracle replayClock temp success.2.1
    have stackGc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk stack.gcFun := by
      have gcEq : stack.gcFun = Flapjack.Compiler.Backend.WordGcFunctions.wordGcFun c := pre.gcFun
      rw [gcEq]
      exact Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.gcFunConstOkWordGcFun
    refine ⟨?_,?_,facts.1,facts.2.1,facts.2.2.1,facts.2.2.2,?_,?_⟩
    · intro loopState
      let compiledCode := sptFromAList (Compiler.Backend.WordToWord.compile wc ac
        (loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2
      let originalCode := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))
      exact (CrepToLoopSteps.nativeEntry_loopWordDataRel_iff ac _ frameSize stack compiledCode originalCode coracle loopState).trans
        (CrepToLoopSteps.nativeEntry_loopWordDataRel_iff ac _ 0 stack compiledCode originalCode coracle loopState).symm
    · exact stackGc
    · simpa using (SteppedFlapjack.WordToStackSteps.nativeTailEntry_loopLocals _
        (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
          (sptFromAList (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
            (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2) coracle :
              WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) frameSize).1
    · exact (SteppedFlapjack.WordToStackSteps.nativeTailEntry_loopLocals _
        (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
          (sptFromAList (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
            (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2) coracle :
              WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) frameSize).2
  · right
    have classification : stackEntryClass (some (.halt (.word 2)) : Option (StackSemResult 64)) =
        .CompleteResult HolOutcome.resourceLimitHit := by simp [stackEntryClass]
    obtain ⟨newPre,newRel,newLabRel,newTie,newMachineRel⟩ :=
      SteppedFlapjack.StackAllocSteps.namedPipelineInitial_setClock
        {stack with code := sptFromAList (StackRawCall.compile inputCode)} renamed lab
        anything cr c stack.regs jump bounds pointer initialClock (limit+1) f
        (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle
        mc machine labCode labs pc asm pre relation rel tie machineRel
    obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
      stackPipelineRiscVWithin inputCode stack firstLoopName (limit+1) 3 (some (.halt (.word 2))) post
        anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle
        {renamed with clock := limit+1} {lab with clock := limit+1} HolOutcome.resourceLimitHit
        pc mc labCode labs asm machine distinct sourceCode run (by simp) stepBound newPre newRel
        ha hs hk hf hcode hor newLabRel hpc classification hmc newTie newMachineRel
    exact ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,by simpa only [ffi] using events⟩

end SteppedFlapjack.PanToCrepSteps
