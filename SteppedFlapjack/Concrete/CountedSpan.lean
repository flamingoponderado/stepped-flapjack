import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals
import SteppedFlapjack.PanToCrepSteps.GlobalShapes
import SteppedFlapjack.PanToCrepSteps.GlobalEntry
import SteppedFlapjack.Concrete.ControlCodeIndependent
import SteppedFlapjack.Concrete.SimpVisits
import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.Concrete.SupportedSpan
import SteppedFlapjack.CrepToLoopSteps.CallFrontendShape
import SteppedFlapjack.LoopToWordSteps.WholeWordSpan

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

private theorem simpTable_lookup
    (source target : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel source target) (name : MlS) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (rsh : ShapeHOL)
    (targetFound : lookupCodeHOLFinite target.lookup name values = some (body,locals,rsh)) :
    ∃ original, lookupCodeHOLFinite source.lookup name values = some (original,locals,rsh) ∧
      body = panSimpCompileHOL original := by
  have lookup := PanSimp.lookupCodeRel source target rel name values
  rw [targetFound] at lookup
  cases found : lookupCodeHOLFinite source.lookup name values with
  | none => simp [found] at lookup
  | some entry =>
    obtain ⟨original,originalLocals,originalShape⟩ := entry
    simp only [found,Option.map_some,Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨bodyEq,localsEq,shapeEq⟩ := lookup
    subst locals
    subst rsh
    exact ⟨original,rfl,bodyEq⟩


/-- A simplified table retains supported bodies when the original table does. -/
theorem simpTable_globalSupported
    (source target : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel source target) (factor : Nat) (table : SimpVisits.SimpTableSupported source factor) :
    GlobalTableSupported target := by
  intro name values body locals rsh targetFound
  obtain ⟨original,found,bodyEq⟩ := simpTable_lookup source target rel name values body locals rsh targetFound
  obtain ⟨scope,program,originalEq,supported,_⟩ := table name values original locals rsh found
  refine ⟨scope,panSimpProg program,?_,callSupported_panSimp supported⟩
  rw [originalEq,callSupported_panSimp_hol supported] at bodyEq
  exact bodyEq

/-- Simplification also preserves representability of supported table bodies. -/
theorem simpTable_rangedSupported
    (source target : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : PanSimp.CodeRel source target)
    (table : ∀ name values body locals rsh, lookupCodeHOLFinite source.lookup name values = some (body,locals,rsh) →
      ∃ scope, ∃ program : Prog (RiscV.Word 64), body = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program) :
    ∀ name values body locals rsh, lookupCodeHOLFinite target.lookup name values = some (body,locals,rsh) →
      ∃ scope, ∃ program : Prog (RiscV.Word 64), body = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program := by
  intro name values body locals rsh targetFound
  obtain ⟨original,found,bodyEq⟩ := simpTable_lookup source target rel name values body locals rsh targetFound
  obtain ⟨scope,program,originalEq,supported,ranged⟩ := table name values original locals rsh found
  refine ⟨scope,panSimpProg program,?_,callSupported_panSimp supported,callSupported_panSimp_ranged supported ranged⟩
  rw [originalEq,callSupported_panSimp_hol supported] at bodyEq
  exact bodyEq

/-- Global lowering preserves the run and visit count of a supported body. -/
private theorem callSupported_globalRun {scope : List VarName} {σ : Type}
    {program : Prog (RiscV.Word 64)} (supported : CallSupportedIn scope program)
    (globals : PanGlobalsContextExact 64) (source sourceFinal target : PanSemStateFiniteExact 64 σ)
    (result : Option (PanSemResultExact 64)) (table : GlobalTableSupported source.code)
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (rel : panGlobalsStateRelHOLExact true globals source target) :
    ∃ targetFinal, target.evaluateHOLFiniteState (progToHOL program) = (result,targetFinal) ∧
      controlSteps (progToHOL program) target = controlSteps (progToHOL program) source ∧
      targetFinal.ffi = sourceFinal.ffi := by
  obtain ⟨targetFinal,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (progToHOL program) source result globals target sourceFinal ⟨rel,run,nonerror⟩
  rw [callSupportedIn_globals_fixed supported globals] at targetRun
  have visits := callSupported_globals_control supported globals source sourceFinal target result table run nonerror rel
  rcases postRel with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,ffi,_,_⟩
  exact ⟨targetFinal,targetRun,visits,ffi.symm⟩

/-- A counted source return reaches the simplified body and related function
  table within a concrete source-derived visit bound. -/
private theorem countedCalls_simplifiedVisits {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (byteRanged : ProgByteRanged program)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body)
    (targetCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (codeRel : PanSimp.CodeRel source.code targetCode) (factor : Nat) (positive : 1 ≤ factor)
    (table : SimpVisits.SimpTableSupported source.code factor)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ) (exnContracts : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ source.clock) :
    ∃ sourceFinal targetFinal,
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      ({source with code := targetCode} : PanSemStateFiniteExact 64 σ).evaluateHOLFiniteState
        (progToHOL (panSimpProg program)) = (some (.returned (.val (.word value))),targetFinal) ∧
      controlSteps (progToHOL (panSimpProg program)) {source with code := targetCode} ≤
        factor * count + SimpVisits.hw (progToHOL (panSimpProg program)) ∧
      targetFinal.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  obtain ⟨holResult,sourceFinal,sourceRun,outcome,sourceBound,_⟩ := supportedCalls_counted_source supported production source
    rel ranged words byteRanged codeRanged codeShape context primitive handler exnContracts fuel count
    (.returned postLocals postGlobals postMemory postFfi [.word value]) run budget
  cases outcome with
  | returned _ _ _ _ _ _ finalRel _ _ =>
    have cost := SimpVisits.callSupported_simp_tableVisits supported source targetCode codeRel factor positive table (by rw [sourceRun]; simp)
    have original : controlSteps (progToHOL program) source ≤ count := by simpa [countedErrorBonus] using sourceBound
    obtain ⟨targetFinal,targetRun,targetRel⟩ := callSupported_panSimp_run supported source sourceFinal {source with code := targetCode}
      (some (.returned (.val (.word value)))) sourceRun (by simp) ⟨rfl,codeRel⟩
    have ffi : targetFinal.ffi = sourceFinal.ffi := by
      simpa using congrArg (fun st : PanSemStateFiniteExact 64 σ => st.ffi) targetRel.1
    refine ⟨sourceFinal,targetFinal,sourceRun,targetRun,?_,ffi,finalRel.2.2.2.2.2.2.2.2.2.2.1⟩
    exact cost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left factor original) _)

/-- The source count bounds visits through simplification, function renaming and global lowering. -/
private theorem countedCalls_renamedGlobalVisits {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (byteRanged : ProgByteRanged program)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body)
    (targetCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (codeRel : PanSimp.CodeRel source.code targetCode)
    (entries : List SimpVisits.SimpEntry)
    (sourceCode : source.code = HolFiniteMapExact.empty.updateList entries.reverse)
    (entryShapes : ∀ entry ∈ entries, ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program)
    (f g : MlS)
    (globals : PanGlobalsContextExact 64) (lower : PanSemStateFiniteExact 64 σ)
    (globalRel : panGlobalsStateRelHOLExact true globals {source with code := fpermCodeHOL f g targetCode} lower)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ) (exnContracts : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ source.clock) :
    ∃ sourceFinal simpFinal lowerFinal,
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      ({source with code := targetCode} : PanSemStateFiniteExact 64 σ).evaluateHOLFiniteState
        (progToHOL (panSimpProg program)) = (some (.returned (.val (.word value))),simpFinal) ∧
      lower.evaluateHOLFiniteState (fpermHOL f g (progToHOL (panSimpProg program))) =
        (some (.returned (.val (.word value))),lowerFinal) ∧
      controlSteps (fpermHOL f g (progToHOL (panSimpProg program))) lower ≤
        SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program)) ∧
      lowerFinal.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  have positive : 1 ≤ SimpVisits.simpTableFactor entries := by simp [SimpVisits.simpTableFactor]
  have table : SimpVisits.SimpTableSupported source.code (SimpVisits.simpTableFactor entries) := by
    rw [sourceCode]
    apply SimpVisits.simpTableSupported_of_entries
    intro entry member
    obtain ⟨scope,program,bodyEq,supported,_⟩ := entryShapes entry member
    exact ⟨scope,program,bodyEq,supported⟩
  have rangedTable := SimpVisits.rangedTableSupported_of_entries entries entryShapes
  rw [← sourceCode] at rangedTable
  obtain ⟨sourceFinal,simpFinal,sourceRun,simpRun,bound,ffi,ffiRel⟩ := countedCalls_simplifiedVisits
    supported production source rel ranged words byteRanged codeRanged codeShape targetCode codeRel (SimpVisits.simpTableFactor entries) positive table
    context primitive handler exnContracts fuel count postLocals postGlobals postMemory postFfi value run budget
  have simpShape := callSupported_panSimp supported
  have simpRanged := callSupported_panSimp_ranged supported byteRanged
  obtain ⟨renamed,renameEq,renameShape⟩ := callSupported_fperm_shape simpShape simpRanged f g
  have simplifiedTable := simpTable_globalSupported source.code targetCode codeRel (SimpVisits.simpTableFactor entries) table
  have renamedTable := fperm_globalTableSupported targetCode f g (simpTable_rangedSupported source.code targetCode codeRel rangedTable)
  have renamedRun := evaluateFpermHOL f g (progToHOL (panSimpProg program)) {source with code := targetCode}
    (some (.returned (.val (.word value)))) simpFinal simpRun
  have renamedCost := callSupported_fperm_control simpShape f g {source with code := targetCode} simplifiedTable
  rw [renameEq] at renamedRun renamedCost
  obtain ⟨lowerFinal,lowerRun,cost,lowerFfi⟩ := callSupported_globalRun renameShape globals
    {source with code := fpermCodeHOL f g targetCode} {simpFinal with code := fpermCodeHOL f g simpFinal.code}
    lower (some (.returned (.val (.word value)))) renamedTable renamedRun (by simp) globalRel
  refine ⟨sourceFinal,simpFinal,lowerFinal,sourceRun,simpRun,?_,?_,?_,ffiRel⟩
  · simpa only [renameEq] using lowerRun
  · rw [renameEq,cost,renamedCost]; exact bound
  · exact lowerFfi.trans ffi

private theorem generatedStores {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) (globals : PanGlobalsContextExact width) :
    ∀ p ∈ (compileDecsExactHOL globals declarations).1, ∃ a v, p = .store a v := by
  induction declarations generalizing globals with
  | nil => simp [compileDecsExactHOL]
  | cons d ds ih =>
    cases d with
    | function fn => simpa only [compileDecsExactHOL] using ih globals
    | exnDecl name shape => simpa only [compileDecsExactHOL] using ih globals
    | name name fields => simpa only [compileDecsExactHOL] using ih globals
    | decl shape name value =>
      simp only [compileDecsExactHOL]
      intro p member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_,_,rfl⟩
      · exact ih _ p member
private theorem storeSeq_static {width : Nat} [NeZero width] {F : Type}
    (inits : List (ProgHOL width))
    (stores : ∀ p ∈ inits, ∃ a v, p = .store a v)
    (state : PanSemStateFiniteExact width F) :
    controlSteps (nestedSeqHOL inits) state ≤ sizeOf (nestedSeqHOL inits) := by
  induction inits generalizing state with
  | nil => simp only [nestedSeqHOL]; rw [controlSteps.eq_def]; simp_wf
  | cons p ps ih =>
    obtain ⟨a,v,rfl⟩ := stores p (by simp)
    have tail : ∀ q ∈ ps, ∃ a v, q = .store a v := by
      intro q h; exact stores q (by simp [h])
    simp only [nestedSeqHOL]
    rw [controlSteps_seq]
    have first : controlSteps (.store a v) state = 1 := by rw [controlSteps.eq_def]; simp_wf
    rw [first]
    rcases state.evaluateHOLFiniteState (.store a v) with ⟨result,post⟩
    cases result with
    | none => have second := ih tail post; simp_wf; omega
    | some result => simp_wf; omega
/-- Generated global initialization has a concrete source-syntax visit bound. -/
private theorem generated_initializers_static {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (globals : PanGlobalsContextExact width)
    (state : PanSemStateFiniteExact width F) :
    controlSteps (nestedSeqHOL (compileDecsExactHOL globals declarations).1) state ≤
      sizeOf (nestedSeqHOL (compileDecsExactHOL globals declarations).1) :=
  storeSeq_static _ (generatedStores declarations globals) state

/-- The generated zero-argument tail entry inherits the counted source bound.
The callee lookup is derived from simplification, renaming and the global-state relation. -/
private theorem countedCalls_renamedGlobalEntry {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (byteRanged : ProgByteRanged program)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body)
    (targetCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (codeRel : PanSimp.CodeRel source.code targetCode)
    (entries : List SimpVisits.SimpEntry)
    (sourceCode : source.code = HolFiniteMapExact.empty.updateList entries.reverse)
    (entryShapes : ∀ entry ∈ entries, ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program)
    (declarations : List (DeclHOL 64)) (f : MlS)
    (initializers : List (ProgHOL 64)) (funs exns : List (DeclHOL 64))
    (globals : PanGlobalsContextExact 64)
    (found : (functionsHOL declarations).lookup f = some ([],progToHOL (panSimpProg program),.one))
    (compiled : let renamed := fpermDecsHOL f (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact 64 :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,globals)) (before middle : PanSemStateFiniteExact 64 σ)
    (initRun : before.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (clock : middle.clock ≠ 0)
    (mainFound : source.code.lookup f = some ([],progToHOL program,.one))
    (globalRel : panGlobalsStateRelHOLExact true globals {source with code := fpermCodeHOL f (newMainNameHOL declarations) targetCode}
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ) (exnContracts : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ source.clock) :
    ∃ (sourceFinal lowerFinal : PanSemStateFiniteExact 64 σ),
      source.evaluateHOLFiniteState (progToHOL program) =
        (some (.returned (.val (.word value))),sourceFinal) ∧
      functionsHOL (compileTopExactHOL declarations f) =
        (f,[],.seq (nestedSeqHOL initializers) (.call none (newMainNameHOL declarations) []),.one) :: functionsHOL funs ∧
      before.evaluateHOLFiniteState (.seq (nestedSeqHOL initializers) (.call none (newMainNameHOL declarations) [])) =
        (some (.returned (.val (.word value))),emptyLocalsHOLFinite lowerFinal) ∧
      globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL declarations) [] before ≤
        sizeOf (nestedSeqHOL initializers) + (SimpVisits.simpTableFactor entries * count +
          SimpVisits.hw (progToHOL (panSimpProg program))) + 2 ∧
      lowerFinal.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  obtain ⟨sourceFinal,simpFinal,lowerFinal,sourceRun,simpRun,lowerRun,bound,ffi,ffiRel⟩ :=
    countedCalls_renamedGlobalVisits supported production source rel ranged words byteRanged codeRanged codeShape
      targetCode codeRel entries sourceCode entryShapes f (newMainNameHOL declarations) globals
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty) globalRel
      context primitive handler exnContracts fuel count postLocals postGlobals postMemory postFfi value run budget
  have targetFound := codeRel.2 f [] (progToHOL program) .one mainFound
  rw [callSupported_panSimp_hol supported] at targetFound
  have renamedFound := flookupFpermCodeHOL f (newMainNameHOL declarations) targetCode f
  rw [targetFound] at renamedFound
  have fixed := callSupportedIn_globals_fixed (callSupported_fperm_shape (callSupported_panSimp supported)
    (callSupported_panSimp_ranged supported byteRanged) f (newMainNameHOL declarations)).choose_spec.2 globals
  have codeRel' := globalRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have lowerFound := codeRel' (fpermName f (newMainNameHOL declarations) f) [] (fpermHOL f (newMainNameHOL declarations) (progToHOL (panSimpProg program))) .one (by simpa using renamedFound)
  have middleFound : middle.code.lookup (fpermName f (newMainNameHOL declarations) f) =
      some ([],fpermHOL f (newMainNameHOL declarations) (progToHOL (panSimpProg program)),.one) := by
    have eq := (callSupported_fperm_shape (callSupported_panSimp supported)
      (callSupported_panSimp_ranged supported byteRanged) f (newMainNameHOL declarations)).choose_spec.1
    rw [eq] at lowerFound
    rw [fixed] at lowerFound
    simpa only [callEntryStateHOLFinite,decClockHOLFinite,← eq] using lowerFound
  have lookup : lookupCodeHOLFinite middle.code.lookup (fpermName f (newMainNameHOL declarations) f) [] =
      some (fpermHOL f (newMainNameHOL declarations) (progToHOL (panSimpProg program)),HolFiniteMapExact.empty,.one) := by
    apply SemInitSupport.lookup_init
    exact middleFound
  have lookup' : lookupCodeHOLFinite middle.code.lookup (newMainNameHOL declarations) [] =
      some (fpermHOL f (newMainNameHOL declarations) (progToHOL (panSimpProg program)),HolFiniteMapExact.empty,.one) := by
    simpa [fpermName] using lookup
  have entry := compileTop_entry_return_with_steps declarations f (progToHOL (panSimpProg program)) .one found
    initializers funs exns globals compiled before middle lowerFinal
    (fpermHOL f (newMainNameHOL declarations) (progToHOL (panSimpProg program))) HolFiniteMapExact.empty .one (.val (.word value))
    (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program)))
    initRun lookup' clock lowerRun (by simp [shapeOfHOLExact,shapeEqHOL]) bound
  let renamed := fpermDecsHOL f (newMainNameHOL declarations) (resortDeclsHOL declarations)
  let initial : PanGlobalsContextExact 64 :=
    { globals := HolFiniteMapExact.empty, globalsSize := 0,
      maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
  have initBound := generated_initializers_static renamed initial before
  rw [show compileDecsExactHOL initial renamed = (initializers,funs,exns,globals) from compiled] at initBound
  dsimp only at initBound
  have entryBound := entry.2.2
  refine ⟨sourceFinal,lowerFinal,sourceRun,entry.1,entry.2.1,?_,ffi,ffiRel⟩
  omega

set_option linter.unnecessarySimpa false in
set_option linter.unnecessarySeqFocus false in
/-- Counted source execution reaches the actual initialized function-only entry. -/
theorem countedCalls_functionOnlyGlobalEntry {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (byteRanged : ProgByteRanged program)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body)
    (targetCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (codeRel : PanSimp.CodeRel source.code targetCode)
    (entries : List SimpVisits.SimpEntry)
    (sourceCode : source.code = HolFiniteMapExact.empty.updateList entries.reverse)
    (entryShapes : ∀ entry ∈ entries, ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program)
    (fs : List (FunDeclHOL 64)) (start : MlS)
    (targetTable : targetCode = HolFiniteMapExact.empty.updateList (functionsHOL (fs.map DeclHOL.function)).reverse)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],progToHOL (panSimpProg program),.one))
    (mainFound : source.code.lookup start = some ([],progToHOL program,.one))
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ) (exnContracts : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ source.clock) :
    let decls := fs.map DeclHOL.function
    let renamed := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
    let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL decls start)).reverse)
    ∃ (sourceFinal lowerFinal : PanSemStateFiniteExact 64 σ),
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      before.evaluateHOLFiniteState (.seq .skip (.call none (newMainNameHOL decls) [])) =
        (some (.returned (.val (.word value))),emptyLocalsHOLFinite lowerFinal) ∧
      globalEntrySteps .skip (newMainNameHOL decls) [] before ≤
        1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2 ∧
      lowerFinal.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  let decls := fs.map DeclHOL.function
  let fresh := newMainNameHOL decls
  let renamed : PanSemStateFiniteExact 64 σ := {source with code := fpermCodeHOL start fresh targetCode}
  let code := HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL decls start)).reverse
  let before := noGlobalsLoweredPreCall renamed code
  have init := functionOnly_source_initialization fs start (progToHOL (panSimpProg program)) .one found renamed
    (by simpa [renamed] using locals) (by simpa [renamed] using globals) (by simpa [renamed] using structs)
    (by simpa [renamed] using topOutside) (by simpa [renamed] using aligned)
    (by simpa [renamed,decls,fresh,targetTable])
  dsimp only at init
  let funs : List (DeclHOL 64) := (fpermDecsHOL start fresh decls).map (fun d => match d with
    | .function f => .function {f with body := compileProgExactHOL emptyGlobalsContext f.body}
    | _ => .name (Flapjack.Basis.Pure.MlString.ofString "") [])
  have compiled := functionOnly_compileDecs fs start fresh
  obtain ⟨sourceFinal,lowerFinal,sourceRun,_,lowerRun,bound,ffi,ffiRel⟩ :=
    countedCalls_renamedGlobalEntry supported production source rel ranged words byteRanged codeRanged codeShape
      targetCode codeRel entries sourceCode entryShapes decls start [] funs [] emptyGlobalsContext found
      (by
        dsimp only [decls,fresh,funs]
        dsimp only at compiled
        convert compiled using 1 <;> congr 2 <;> simp [fresh,decls]
        intro d hd
        cases d <;> rfl) before before init.1 init.2.1 mainFound init.2.2
      context primitive handler exnContracts fuel count postLocals postGlobals postMemory postFfi value run budget
  exact ⟨sourceFinal,lowerFinal,sourceRun,lowerRun,by simpa [nestedSeqHOL] using bound,ffi,ffiRel⟩

/-- A call-aware counted source return composes with the actual declaration
frontend, carrying the source count into the Crep visit bound. -/
theorem callFrontend_counted_declaration_steps {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (byteRanged : ProgByteRanged program)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body)
    (declarations : List (DeclHOL 64))
    (unique : ((functionsHOL declarations).map Prod.fst).Nodup)
    (noInline : (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1)
    (frontend : CallFrontend (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)) (progToHOL program))
    (code : source.code = HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (noExceptions : getEidsFromDeclsHOL declarations = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ) (exnContracts : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ source.clock) :
    let ctxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)
    let programs := compileProgDeclsHOLW declarations
    ∃ sourceFinal targetFinal,
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      evalCrepSemHOLProgExact (concreteDeclCrepState source programs) (compileProgExactHOLW ctxt (progToHOL program)) =
        (some (.return [.word value]),targetFinal) ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (progToHOL program)) (concreteDeclCrepState source programs) ≤
        max (CrepSteps.statementWeight (compileProgExactHOLW ctxt (progToHOL program))) (CrepSteps.codeWeight programs) * count ∧
      targetFinal.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  obtain ⟨holResult,sourceFinal,sourceRun,outcome,sourceBound,_⟩ := supportedCalls_counted_source supported production source
    rel ranged words byteRanged codeRanged codeShape context primitive handler exnContracts fuel count
    (.returned postLocals postGlobals postMemory postFfi [.word value]) run budget
  cases outcome with
  | returned _ _ _ _ _ _ finalRel _ _ =>
    have span := callFrontend_declaration_steps declarations unique noInline shapes (progToHOL program) frontend
      source sourceFinal (some (.returned (.val (.word value)))) code locals globals structs exceptions noExceptions sourceRun
      (by simp) count (by simpa [countedErrorBonus] using sourceBound)
    obtain ⟨targetResult,targetFinal,targetRun,finalState,_,_,resultRel,bound⟩ := span
    have resultEq : targetResult = some (.return [.word value]) := by
      simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
    subst targetResult
    rcases finalState with ⟨_,_,_,_,_,_,_,ffi,_,_⟩
    exact ⟨sourceFinal,targetFinal,sourceRun,by simpa [flattenHOL] using targetRun,bound,ffi.symm,finalRel.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Counted source execution reaches the optimized Word start call at an explicit bound. -/
theorem callFrontend_counted_optimizedStart {C σ : Type} {scope : List VarName}
    (declarations : List (DeclHOL 64))
    (unique : ((functionsHOL declarations).map Prod.fst).Nodup)
    (noInline : (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1)
    (program : Prog (RiscV.Word 64)) (supported : CallSupportedIn scope program)
    (shape : CallFrontend (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)) (progToHOL program))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs] (value : BitVec 64)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (words : WordLocals production.locals) (byteRanged : ProgByteRanged program)
    (codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body)
    (code : source.code = HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (noExceptions : getEidsFromDeclsHOL declarations = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ) (exnContracts : InfoMap Shape) (fuel sourceLimit : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],sourceLimit))
    (budget : sourceLimit ≤ source.clock)
    (arch : AsmArchitecture) (start : Flapjack.Basis.Pure.MlString.MlString) (entry : CrepProgHOL 64)
    (found : holAlookup (compileProgDeclsHOLW declarations) start = some ([],entry))
    (ref : CrepToLoopContextExact) (live : NumSet) (loop : LoopSemStateFiniteExact 64 σ)
    (loopCode : loop.code = sptFromAList (compileProgHOLExact arch (compileProgDeclsHOLW declarations)))
    (stateRel : crepToLoopStateRelExact (concreteDeclCrepState source (compileProgDeclsHOLW declarations)) loop)
    (memRel : crepToLoopMemRelHOLExact (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).memory
      loop.memory (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).globals loop.globals)
    (localsRel : crepToLoopLocalsRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW declarations)) 0)
      live (concreteDeclCrepState source (compileProgDeclsHOLW declarations)).locals loop.locals)
    (starter : WordSemStateFiniteExact 64 C σ) (entryLoc : Nat) (wordCtxt : Spt Nat) (label : Nat × Nat)
    (wc : Config) (ac : AsmConfigExact 64)
    (starterCode : starter.code = sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW declarations))))
    (arg : getVar 0 starter = some (.loc 1 0)) (stack : starter.stack = [])
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk starter.gcFun)
    (entryMember : let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0 (getEidsFromDeclsHOL declarations)
      let programs := compileProgDeclsHOLW declarations
      let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
      let body := (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (compileProgExactHOLW panCtxt (progToHOL program))) label).1
      (entryLoc,1,body) ∈ loopToWordCompileHOL (compileProgHOLExact arch programs))
    (wordRel : let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0 (getEidsFromDeclsHOL declarations)
      let programs := compileProgDeclsHOLW declarations
      let crep := compileProgExactHOLW panCtxt (progToHOL program)
      let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * sourceLimit
      let rows := programs.map (fun row => (row.2.1,row.2.2))
      let budget := callClockFactor ref rows source.clock crep * (limit+1)
      let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup entryLoc starter.stackSize) (decClock starter)
      loopToWordStateRelHOLExact {loop with clock := loop.clock+budget} word)
    (wordLocals : LoopToWord.localsRelHOL wordCtxt loop.locals
      (callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup entryLoc starter.stackSize) (decClock starter)).locals)
    (acc : ∀ k, sptMem k (accVarsHOL (compileHOLExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW declarations)) 0) live
      (compileProgExactHOLW (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
        (getEidsFromDeclsHOL declarations)) (progToHOL program))) .ln) → sptMem k wordCtxt) :
    let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)
    let programs := compileProgDeclsHOLW declarations
    let crep := compileProgExactHOLW panCtxt (progToHOL program)
    let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * sourceLimit
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let budget := callClockFactor ref rows source.clock crep * (limit+1)
    let factor := max (callSyntaxCost ref crep) (loopCodeWeight loop.code+2)
    let ticks := 6 * (callSyntaxCost ref crep + factor * (source.clock+budget))
    let rawWords := loopToWordCompileHOL (compileProgHOLExact arch programs)
    ∃ sourceFinal final, source.evaluateHOLFiniteState (progToHOL program) =
        (some (.returned (.val (.word value))),sourceFinal) ∧
      FfiStateRel postFfi sourceFinal.ffi ∧ evaluate (.call none (some entryLoc) [0] none)
        {starter with clock := ticks+1, code := sptFromAList (compile wc ac rawWords).2} =
          (some (.result (.loc 1 0) [.word value]),final) ∧
      final.ffi = sourceFinal.ffi ∧
      WordSteps.steps (.call none (some entryLoc) [0] none)
        {starter with clock := ticks+1, code := sptFromAList (compile wc ac rawWords).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac rawWords).2)) * (ticks+1) := by
  obtain ⟨holResult,sourceFinal,sourceRun,outcome,sourceBound,_⟩ := supportedCalls_counted_source supported production source
    rel ranged words byteRanged codeRanged codeShape context primitive handler exnContracts fuel sourceLimit
    (.returned postLocals postGlobals postMemory postFfi [.word value]) run budget
  cases outcome with
  | returned _ _ _ _ _ _ finalRel _ _ =>
    obtain ⟨final,wordRun,ffi,bound⟩ := callFrontend_declaration_optimizedStart declarations unique noInline shapes
      (progToHOL program) shape source sourceFinal value code locals globals structs exceptions noExceptions sourceRun
      sourceLimit (by simpa [countedErrorBonus] using sourceBound) arch start entry found ref live loop loopCode
      stateRel memRel globalsRel localsRel starter entryLoc wordCtxt label wc ac starterCode arg stack gc entryMember
      wordRel wordLocals acc
    exact ⟨sourceFinal,final,sourceRun,finalRel.2.2.2.2.2.2.2.2.2.2.1,wordRun,ffi,bound⟩

/-- Every counted supported run, including errors, reaches the actual
simplified and global-lowered callee with the same source result. -/
theorem supported_counted_frontend_prefix {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let simplified := panSimpProg program
    let body := progToHOL simplified
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let simplifiedSource := panSimpSourceState program source
    let lower := callEntryStateHOLFinite (loweredStateFrom simplifiedSource body) HolFiniteMapExact.empty
    ∃ holResult sourceFinal,
      CountedOutcome production result holResult sourceFinal ∧
      lower.evaluateHOLFiniteState body =
        (holResult,{{sourceFinal with code := simplifiedSource.code} with code := (loweredStateFrom simplifiedSource body).code}) ∧
      controlSteps body lower ≤ n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body) := by
  let simplified := panSimpProg program
  let body := progToHOL simplified
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let simplifiedSource := panSimpSourceState program source
  let lower := callEntryStateHOLFinite (loweredStateFrom simplifiedSource body) HolFiniteMapExact.empty
  obtain ⟨holResult,sourceFinal,sourceRun,outcome,countedBound,_⟩ := supported_counted_source supported.1 production source
    rel ranged words supported.2 context primitive handler functions fuel count result run (by omega)
  let simplifiedFinal := {sourceFinal with code := simplifiedSource.code}
  have simpRun := supported_panSimp_run program supported source sourceFinal holResult sourceRun
  have shape := (supported_panSimp program supported).1
  have lowerRun := supported_globals_run_from simplified shape simplifiedSource simplifiedFinal holResult
    (by simpa [simplifiedSource,panSimpSourceState] using locals) simpRun
  have lowerEq : lower = {source with code := lower.code} := by
    simp [lower,loweredStateFrom,noGlobalsLoweredPreCall,callEntryStateHOLFinite,
      simplifiedSource,panSimpSourceState,locals]
  have independent := supported_control_code_irrel shape source lower.code
  have simplifiedBound := SimpVisits.supported_panSimp_controlSteps_compiled program supported callee source
  change controlSteps body source ≤ controlSteps (progToHOL program) source +
    CrepSteps.statementWeight (compileProgExactHOLW callee body) at simplifiedBound
  have bonusBound : countedErrorBonus result ≤ 1 := by
    cases result <;> simp [countedErrorBonus]
  refine ⟨holResult,sourceFinal,outcome,lowerRun,?_⟩
  change controlSteps body lower ≤ n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)
  rw [lowerEq,independent]
  change controlSteps body source ≤ n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)
  omega

/-- The observable result of a call to a supported body: a fallthrough is a
call error; a word return is preserved. -/
inductive CountedEntryExit {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Option (BitVec 64) → Prop
  | normal (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) :
      CountedEntryExit (.normal locals globals memory ffi) none
  | returned (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (word : BitVec 64) :
      CountedEntryExit (.returned locals globals memory ffi [.word word]) (some word)
  | error (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) :
      CountedEntryExit (.error locals globals memory ffi) none

/-- Error runs may require up to three compiled visits per source visit. -/
def countedFrontendFactor {σ : Type} (result : PanValueFfiControlResult (RiscV.Word 64) σ) : Nat :=
  1 + 2 * countedErrorBonus result

/-- Every counted body run reaches the generated entry within a
concrete code-derived bound. The exit relation records whether the function
returned a word, fell through, or errored; fallthrough and source errors
produce an error at the generated call entry. -/
theorem supported_counted_full_frontend_exit {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let body := progToHOL (panSimpProg program)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ exit targetFinal,
      CountedEntryExit result exit ∧
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry =
        (bodyExitEntry exit,targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + countedFrontendFactor result * CrepSteps.statementWeight (compileProgExactHOLW callee body) *
          (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) := by
  let simplified := panSimpProg program
  let body := progToHOL simplified
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let simplifiedSource := panSimpSourceState program source
  let lower := loweredStateFrom simplifiedSource body
  obtain ⟨holResult,sourceFinal,outcome,lowerRun,control⟩ := supported_counted_frontend_prefix program supported
    production source rel ranged words locals context primitive handler functions fuel count n result run countBound clock
  let lowerFinal := {{sourceFinal with code := simplifiedSource.code} with code := lower.code}
  have shape := (supported_panSimp program supported).1
  have sourceLocals : simplifiedSource.locals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using locals
  have sourceGlobals : simplifiedSource.globals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using globals
  have sourceStructs : simplifiedSource.structs = [] := by simpa [simplifiedSource,panSimpSourceState] using structs
  have sourceExceptions : simplifiedSource.eshapes = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using exceptions
  cases outcome with
  | normal l g m f final finalRel finalRanged finalWords =>
    have span := supported_entry_crep_exit_from simplified shape simplifiedSource sourceLocals sourceGlobals sourceStructs sourceExceptions
      lowerFinal none (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    obtain ⟨targetFinal,targetRun,bound,_⟩ := span
    exact ⟨none,targetFinal,.normal l g m f,targetRun,by simpa [countedFrontendFactor,countedErrorBonus] using bound⟩
  | returned l g m f word final finalRel finalRanged finalWords =>
    have span := supported_entry_crep_exit_from simplified shape simplifiedSource sourceLocals sourceGlobals sourceStructs sourceExceptions
      lowerFinal (some word) (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    obtain ⟨targetFinal,targetRun,bound,_⟩ := span
    exact ⟨some word,targetFinal,.returned l g m f word,targetRun,by simpa [countedFrontendFactor,countedErrorBonus] using bound⟩
  | error l g m f final finalRel finalRanged finalWords =>
    have span := supported_entry_crep_error_from simplified shape simplifiedSource sourceLocals sourceGlobals sourceStructs sourceExceptions
      lowerFinal (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    obtain ⟨targetFinal,targetRun,bound⟩ := span
    exact ⟨none,targetFinal,.error l g m f,targetRun,by simpa [countedFrontendFactor,countedErrorBonus,bodyExitEntry] using bound⟩

/-- A result-independent bound calculated from the generated code and source budget. -/
theorem supported_counted_full_frontend_uniform {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let body := progToHOL (panSimpProg program)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ exit targetFinal,
      CountedEntryExit result exit ∧
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry =
        (bodyExitEntry exit,targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + 3 * CrepSteps.statementWeight (compileProgExactHOLW callee body) *
          (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) := by
  obtain ⟨exit,targetFinal,outcome,targetRun,bound⟩ := supported_counted_full_frontend_exit
    program supported production source rel ranged words locals globals structs exceptions context primitive handler
    functions fuel count n result run countBound clock
  refine ⟨exit,targetFinal,outcome,targetRun,?_⟩
  have factorBound : countedFrontendFactor result ≤ 3 := by
    cases result <;> simp [countedFrontendFactor,countedErrorBonus]
  have scaled := Nat.mul_le_mul_right
    (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW (ctxtFcExactHOL
      (frontendContext (progToHOL (panSimpProg program))).funcs
      (frontendContext (progToHOL (panSimpProg program))).eids [] [] []) (progToHOL (panSimpProg program))))
    (Nat.mul_le_mul_right
      (CrepSteps.statementWeight (compileProgExactHOLW (ctxtFcExactHOL
        (frontendContext (progToHOL (panSimpProg program))).funcs
        (frontendContext (progToHOL (panSimpProg program))).eids [] [] []) (progToHOL (panSimpProg program))))
      factorBound)
  exact bound.trans (Nat.add_le_add_left scaled 3)

/-- A counted source run bounded by `n` reaches the actual generated entry
point within a bound calculated from `n` and the generated function body. -/
theorem supported_counted_full_frontend {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count n : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState σ) (word : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count))
    (countBound : count ≤ n) (clock : source.clock = n) :
    let body := progToHOL (panSimpProg program)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry =
        (some (.return [.word word]),targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + CrepSteps.statementWeight (compileProgExactHOLW callee body) *
          (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) ∧
      FfiStateRel postFfi targetFinal.ffi := by
  let simplified := panSimpProg program
  let body := progToHOL simplified
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let simplifiedSource := panSimpSourceState program source
  let lower := loweredStateFrom simplifiedSource body
  obtain ⟨holResult,sourceFinal,outcome,lowerRun,control⟩ := supported_counted_frontend_prefix program supported
    production source rel ranged words locals context primitive handler functions fuel count n
    (.returned postLocals postGlobals postMemory postFfi [.word word]) run countBound clock
  let lowerFinal := {{sourceFinal with code := simplifiedSource.code} with code := lower.code}
  have shape := (supported_panSimp program supported).1
  have sourceLocals : simplifiedSource.locals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using locals
  have sourceGlobals : simplifiedSource.globals = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using globals
  have sourceStructs : simplifiedSource.structs = [] := by simpa [simplifiedSource,panSimpSourceState] using structs
  have sourceExceptions : simplifiedSource.eshapes = HolFiniteMapExact.empty := by simpa [simplifiedSource,panSimpSourceState] using exceptions
  cases outcome with
  | returned l g m f value final finalRel finalRanged finalWords =>
    obtain ⟨targetFinal,targetRun,bound,ffi⟩ := supported_entry_crep_exit_from simplified shape simplifiedSource
      sourceLocals sourceGlobals sourceStructs sourceExceptions lowerFinal (some word)
      (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) lowerRun control
    have ffiRel : FfiStateRel postFfi sourceFinal.ffi := finalRel.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨targetFinal,targetRun,bound,?_⟩
    simpa [lowerFinal] using ffi ▸ ffiRel

end SteppedFlapjack.Concrete
