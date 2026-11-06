import SteppedFlapjack.PanToCrepSteps.GlobalCrepEntry
import SteppedFlapjack.CrepToLoopSteps.SimpFixed
import SteppedFlapjack.WordAllocSteps.WholeTailCode
import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas

/-! The real global wrapper reaches the actual whole-program Word input. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open SteppedFlapjack.CrepToLoopSteps

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

end SteppedFlapjack.PanToCrepSteps
