import SteppedFlapjack.PanToCrepSteps.GlobalTailWord
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.LoopToWordSteps.WholeCodeRel
import SteppedFlapjack.WordAllocSteps.WholeFrontendShapes
import SteppedFlapjack.CrepToLoopSteps.WholeInitialRelations

/-! Code relations for the actual generated global-entry program. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open SteppedFlapjack.CrepToLoopSteps

/-- The actual global entry provides the start lookup needed to derive the
Crep/Loop relation; the Loop/Word code relation is compiler-generated. -/
theorem globalEntry_nonInline_frontend_codeRelations {width : Nat} [NeZero width] {F : Type}
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
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (shapes : ∀ name params body, (name,params,body) ∈ compileProgDeclsHOLW (compileTopExactHOL declarations start) →
      CrepToLoopSteps.SupportedCodeBody body) :
    let lowered := compileTopExactHOL declarations start
    let code := compileProgDeclsHOLW lowered
    let loopContext := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable code) 0
    crepToLoopCodeRelExact loopContext (alistToFmapCodeExact code)
      (sptFromAList (compileProgHOLExact arch code)) ∧
    loopToWordCodeRelHOLExact (sptFromAList (compileProgHOLExact arch code))
      (sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch code))) ∧
    WordAllocSteps.TailProgramShapes (loopToWordCompileHOL (compileProgHOLExact arch code)) := by
  obtain ⟨bound,entry,_⟩ := globalEntry_nonInline_preserved declarations start initializers returnShape original found
    funs exns context compiled initShape notInline state
  let code := compileProgDeclsHOLW (compileTopExactHOL declarations start)
  let sourceContext : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
    (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
  let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
  have lookup : holAlookup code start = some ([],.seq init (.call none (newMainNameHOL declarations) [])) := by
    cases h : code with
    | nil => simp [code,h] at bound
    | cons first rest =>
      have firstEq : first = (start,[],.seq init (.call none (newMainNameHOL declarations) [])) := by
        simpa [code,h,init,sourceContext] using entry
      simp [holAlookup,firstEq]
  exact ⟨wholeCrep_supported_executable_codeRel arch code start _ unique lookup shapes,
    LoopToWordSteps.wholeCrepLoopWord_codeRel arch code,
    WordAllocSteps.wholeCrep_word_shapes arch code shapes⟩

/-- The actual global wrapper is the first lookup in the compiled Crep table. -/
theorem globalEntry_nonInline_crep_lookup {width : Nat} [NeZero width] {F : Type}
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
 :
    let lowered := compileTopExactHOL declarations start
    let code := compileProgDeclsHOLW lowered
    let sourceContext : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
    holAlookup code start = some ([],.seq init (.call none (newMainNameHOL declarations) [])) := by
  obtain ⟨bound,entry,_⟩ := globalEntry_nonInline_preserved declarations start initializers returnShape original found
    funs exns context compiled initShape notInline state
  let code := compileProgDeclsHOLW (compileTopExactHOL declarations start)
  let sourceContext : PanToCrepContextExact width := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
    (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
  let init := compileProgExactHOLW sourceContext (nestedSeqHOL initializers)
  change holAlookup code start = some ([],.seq init (.call none (newMainNameHOL declarations) []))
  cases h : code with
  | nil => simp [code,h] at bound
  | cons first rest =>
    have firstEq : first = (start,[],.seq init (.call none (newMainNameHOL declarations) [])) := by
      simpa [code,h,init,sourceContext] using entry
    simp [holAlookup,firstEq]

/-- Actual global-program code tables complete both frontend state relations. -/
theorem globalEntry_nonInline_frontend_stateRelations {width : Nat} [NeZero width] {C F : Type}
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
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (shapes : ∀ name params body, (name,params,body) ∈ compileProgDeclsHOLW (compileTopExactHOL declarations start) →
      CrepToLoopSteps.SupportedCodeBody body)
    (loop : LoopSemStateFiniteExact width F) (word : WordSemStateFiniteExact width C F)
    (sourceState : crepToLoopStateRelExact state loop)
    (memory : crepToLoopMemRelHOLExact state.memory loop.memory state.memaddrs)
    (globals : crepToLoopGlobalsRelHOLExact state.globals loop.globals)
    (locals : crepToLoopLocalsRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0) .ln state.locals loop.locals)
    (data : CrepToLoopSteps.LoopWordDataRel loop word) :
    let lowered := compileTopExactHOL declarations start
    let code := compileProgDeclsHOLW lowered
    let loopContext := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable code) 0
    let source := {state with code := alistToFmapCodeExact code}
    let loop := {loop with code := sptFromAList (compileProgHOLExact arch code)}
    let word := {word with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch code))}
    crepToLoopStateRelExact source loop ∧
    crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs ∧
    crepToLoopGlobalsRelHOLExact source.globals loop.globals ∧
    crepToLoopLocalsRelExact loopContext .ln source.locals loop.locals ∧
    crepToLoopCodeRelExact loopContext source.code loop.code ∧
    loopToWordStateRelHOLExact loop word ∧
    WordAllocSteps.TailProgramShapes (loopToWordCompileHOL (compileProgHOLExact arch code)) := by
  obtain ⟨crepCode,loopCode,wordShapes⟩ := globalEntry_nonInline_frontend_codeRelations arch declarations start
    initializers returnShape original found funs exns context compiled initShape notInline state unique shapes
  obtain ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals⟩ := data
  exact ⟨sourceState,memory,globals,locals,crepCode,
    ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals,loopCode⟩,wordShapes⟩

end SteppedFlapjack.PanToCrepSteps
