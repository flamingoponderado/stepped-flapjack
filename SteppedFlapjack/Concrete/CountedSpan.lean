import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals
import SteppedFlapjack.PanToCrepSteps.GlobalShapes
import SteppedFlapjack.PanToCrepSteps.GlobalEntry
import SteppedFlapjack.Concrete.ControlCodeIndependent
import SteppedFlapjack.Concrete.SimpVisits
import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.Concrete.WordStarter
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopNames
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

/-- A counted source return reaches the compiler-generated Crep entry at an explicit bound. -/
theorem countedCalls_functionOnlyCrep {scope : List VarName} {program : Prog (RiscV.Word 64)}
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
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (unique : ((functionsHOL (fs.map DeclHOL.function)).map Prod.fst).Nodup)
    (shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ body : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (Flapjack.Basis.Pure.MlString.ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL body ∧ CallSupportedIn names body ∧ ProgByteRanged body)
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
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
    let lowered := compileTopExactHOL decls start
    let renamed := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
    let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
    let entry : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
    let ctxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
    let programs := compileProgDeclsHOLW lowered
    let crep := compileProgExactHOLW ctxt entry
    let limit := 1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2
    ∃ (sourceFinal lowerFinal : PanSemStateFiniteExact 64 σ) (targetFinal : CrepSemHOLState 64 σ),
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      before.evaluateHOLFiniteState entry = (some (.returned (.val (.word value))),emptyLocalsHOLFinite lowerFinal) ∧
      evalCrepSemHOLProgExact (concreteDeclCrepState before programs) crep = (some (.return [.word value]),targetFinal) ∧
      CrepSteps.steps crep (concreteDeclCrepState before programs) ≤
        max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) * limit ∧
      targetFinal.ffi = lowerFinal.ffi ∧ lowerFinal.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  let decls := fs.map DeclHOL.function
  let lowered := compileTopExactHOL decls start
  let renamed : PanSemStateFiniteExact 64 σ := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let entry : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
  let ctxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let programs := compileProgDeclsHOLW lowered
  let limit := 1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2
  obtain ⟨sourceFinal,lowerFinal,sourceRun,lowerRun,lowerBound,lowerFfi,ffiRel⟩ :=
    countedCalls_functionOnlyGlobalEntry supported production source rel ranged words byteRanged codeRanged codeShape
      targetCode codeRel entries sourceCode entryShapes fs start targetTable found mainFound locals globals structs
      topOutside aligned context primitive handler exnContracts fuel count postLocals postGlobals postMemory postFfi value run budget
  have uniqueLowered : ((functionsHOL lowered).map Prod.fst).Nodup := allDistinctCompileTopHOL start decls unique
  have shapeTable := functionOnly_callFrontend_shapes fs start (progToHOL (panSimpProg program)) .one found shapes
  have shapeEntry : CallFrontend ctxt entry := .seq (.base .skip) (.tail (by simp))
  have noEx : getEidsFromDeclsHOL lowered = HolFiniteMapExact.empty := functionOnly_noExceptions fs start _ .one found
  have span := callFrontend_declaration_steps lowered uniqueLowered noInline shapeTable entry shapeEntry before
    (emptyLocalsHOLFinite lowerFinal) (some (.returned (.val (.word value)))) rfl
    (by simpa [before,noGlobalsLoweredPreCall,renamed] using locals)
    (by simpa [before,noGlobalsLoweredPreCall,renamed] using globals)
    (by simpa [before,noGlobalsLoweredPreCall,renamed] using structs)
    (by simpa [before,noGlobalsLoweredPreCall,renamed] using exceptions)
    noEx lowerRun (by simp) limit lowerBound
  obtain ⟨targetResult,targetFinal,targetRun,finalState,_,_,resultRel,visitBound⟩ := span
  have resultEq : targetResult = some (.return [.word value]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst targetResult
  rcases finalState with ⟨_,_,_,_,_,_,_,targetFfi,_,_⟩
  exact ⟨sourceFinal,lowerFinal,targetFinal,sourceRun,lowerRun,by simpa [flattenHOL] using targetRun,visitBound,
    by simpa [emptyLocalsHOLFinite] using targetFfi.symm,lowerFfi,ffiRel⟩

/-- The compiler-generated wrapper is the first generated Crep function. -/
theorem functionOnly_wrapper_first (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = []) :
    ∃ rest, compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start) =
      (start,[],compileProgExactHOLW (mkCtxtExactHOL HolFiniteMapExact.empty
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start))) 0
        (getEidsFromDeclsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)))
        (.seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) []))) :: rest := by
  simp only [compileProgDeclsHOLW,noInline,CrepInlineRoute.compileInlTopHOLExact_nil,compileToCrepExactHOLW]
  rw [functionOnly_compileTop_functions fs start body .one found]
  have emptyUpdate : (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ShapeHOL × List Nat)).updateList [] = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro k
    simp [HolFiniteMapExact.lookup_updateList,FUPDATE_LIST]
  simp [crepVarsHOL,compFuncExactHOLW,panToCrepMakeVmapHOLExact,sizeOfShapeHOL,emptyUpdate]

theorem functionOnly_wrapper_lookup (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = []) :
    holAlookup (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)) start =
      some ([],compileProgExactHOLW (mkCtxtExactHOL HolFiniteMapExact.empty
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start))) 0
        (getEidsFromDeclsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)))
        (.seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) []))) := by
  obtain ⟨rest,first⟩ := functionOnly_wrapper_first fs start body found noInline
  rw [first]
  simp [holAlookup]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- Concrete function declarations derive the whole-table Crep-to-Loop entry relations. -/
theorem functionOnlyCrep_toLoop {σ : Type} (fs : List (FunDeclHOL 64)) (start : MlS)
    (body : ProgHOL 64) (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (unique : ((functionsHOL (fs.map DeclHOL.function)).map Prod.fst).Nodup)
    (shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ program : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (Flapjack.Basis.Pure.MlString.ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL program ∧ CallSupportedIn names program ∧ ProgByteRanged program)
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (source : CrepSemHOLState 64 σ) (final : CrepSemHOLState 64 σ) (value : BitVec 64) (limit : Nat)
    (sourceLocals : source.locals = HolFiniteMapExact.empty)
    (sourceGlobals : source.globals = HolFiniteMapExact.empty)
    (arch : AsmArchitecture) (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact source.memory memory source.memaddrs)
    (code : source.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
    (run : evalCrepSemHOLProgExact source (compileProgExactHOLW (mkCtxtExactHOL HolFiniteMapExact.empty
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start))) 0
        (getEidsFromDeclsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)))
        (.seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) []))) = (some (.return [.word value]),final))
    (bound : CrepSteps.steps (compileProgExactHOLW (mkCtxtExactHOL HolFiniteMapExact.empty
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start))) 0
        (getEidsFromDeclsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)))
        (.seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) []))) source ≤ limit) :
    let decls := compileTopExactHOL (fs.map DeclHOL.function) start
    let programs := compileProgDeclsHOLW decls
    let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
    let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
    let crep := compileProgExactHOLW pan p
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let loop := {(concreteDeclLoopState arch source programs) with memory := memory}
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let budget := callClockFactor ctxt rows source.clock crep * (limit+1)
    let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
    ∃ post, evaluate (compileHOLExact ctxt .ln crep) {loop with clock := loop.clock+budget} =
        (some (.result [.word value]),post) ∧ post.ffi = final.ffi ∧
      LoopSteps.steps (compileHOLExact ctxt .ln crep) {loop with clock := loop.clock+budget} ≤
        callSyntaxCost ctxt crep + factor * (source.clock+budget) := by
  let decls := compileTopExactHOL (fs.map DeclHOL.function) start
  let programs := compileProgDeclsHOLW decls
  let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let loop := {(concreteDeclLoopState arch source programs) with memory := memory}
  have shape : CallFrontend pan p := .seq (.base .skip) (.tail (by simp))
  have shapes' := functionOnly_callFrontend_shapes fs start body .one found shapes
  have sources := callFrontend_declaration_sources decls shapes'
  have sources' : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q := by
    dsimp only [programs]
    rw [compileProgDeclsHOLW,noInline,CrepInlineRoute.compileInlTopHOLExact_nil]
    exact sources
  have unique' : ((functionsHOL decls).map Prod.fst).Nodup := allDistinctCompileTopHOL start (fs.map DeclHOL.function) unique
  have wrapperFound := functionOnly_wrapper_lookup fs start body found noInline
  have codeRel : crepToLoopCodeRelExact ctxt source.code loop.code := by
    rw [code]
    exact callFrontend_declaration_crepLoop_codeRel arch decls noInline shapes' start _ unique' wrapperFound
  have table : LoopTableSupported loop.code := callFrontend_declaration_loopTableSupported arch decls noInline shapes'
  have relations := concreteDecl_crepLoop_relations arch source programs sourceGlobals
  have locals : crepToLoopLocalsRelExact ctxt .ln source.locals loop.locals := by
    rw [sourceLocals]
    apply empty_crepLoop_locals
    rfl
  obtain ⟨post,ev,visits,stateRel,_,_,_,_⟩ := callFrontend_wholeVisits_explicit pan p shape programs sources' ctxt ctxt .ln
    source final (some (.return [.word value])) loop code run (by simp) (by simp) limit bound
    relations.1 memoryRel relations.2.2 codeRel table locals
  exact ⟨post,by simpa [p,resultToLoop,wlabWlocExact] using ev,stateRel.2.2.2.2.1.symm,visits⟩

/-- A first Crep function supplies the first optimized Loop function. -/
theorem firstCrep_loopEntry (arch : AsmArchitecture) (start : MlS) (crep : CrepProgHOL 64)
    (rest : List (MlS × List Nat × CrepProgHOL 64)) (fixed : crepSimpProgHOL crep = crep) :
    let programs := (start,[],crep) :: rest
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    ∃ tail, compileProgHOLExact arch programs =
      (firstLoopName,[],optimiseHOL (compileHOLExact ctxt .ln crep)) :: tail := by
  simp only [compileProgHOLExact,List.length_cons,List.range_succ_eq_map,List.map_cons,List.zipWith_cons_cons,
    Nat.zero_add, List.length_nil, List.range_zero, compFuncHOLExact, listToNumSetHOLExact, fixed]
  exact ⟨_, rfl⟩

/-- The actual generated start wrapper appears in the Loop-to-Word input. -/
theorem functionOnly_wordEntry (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (arch : AsmArchitecture) :
    let decls := compileTopExactHOL (fs.map DeclHOL.function) start
    let programs := compileProgDeclsHOLW decls
    let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
    let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
    let crep := compileProgExactHOLW pan p
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    (firstLoopName,1,loopToWordCompFuncHOL firstLoopName [] (optimiseHOL (compileHOLExact ctxt .ln crep))) ∈
      loopToWordCompileHOL (compileProgHOLExact arch programs) := by
  let decls := compileTopExactHOL (fs.map DeclHOL.function) start
  let programs := compileProgDeclsHOLW decls
  let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
  let crep := compileProgExactHOLW pan p
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  have shape : CallFrontend pan p := .seq (.base .skip) (.tail (by simp))
  have fixed : crepSimpProgHOL crep = crep := callFrontend_simp_fixed shape
  obtain ⟨rest,first⟩ := functionOnly_wrapper_first fs start body found noInline
  have loopFirst := firstCrep_loopEntry arch start crep rest fixed
  have programEq : programs = (start,[],crep) :: rest := first
  rw [← programEq] at loopFirst
  obtain ⟨tail,loopEq⟩ := loopFirst
  change (firstLoopName,1,loopToWordCompFuncHOL firstLoopName [] (optimiseHOL (compileHOLExact ctxt .ln crep))) ∈
    loopToWordCompileHOL (compileProgHOLExact arch programs)
  rw [loopEq]
  simp [loopToWordCompileHOL,loopToWordCompileProgHOL,ctxt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- A generated function-only entry reaches its actual optimized Word start. -/
theorem functionOnly_optimizedWord {C σ : Type} (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ program : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (Flapjack.Basis.Pure.MlString.ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL program ∧ CallSupportedIn names program ∧ ProgByteRanged program)
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (arch : AsmArchitecture) (source : CrepSemHOLState 64 σ) (template : WordSemStateFiniteExact 64 C σ)
    (heapLength : BitVec 64) (frame : Nat) (wc : Config) (ac : AsmConfigExact 64)
    (memory : BitVec 64 → WordLocW 64) (limit : Nat) (value : BitVec 64) (loopPost : LoopSemStateFiniteExact 64 σ)
    (heap : source.topAddr = source.baseAddr + 2 * heapLength)
    (run : let decls := compileTopExactHOL (fs.map DeclHOL.function) start
      let programs := compileProgDeclsHOLW decls
      let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
      let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
      let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
      evaluate (optimiseHOL (compileHOLExact ctxt .ln (compileProgExactHOLW pan p)))
        {(concreteDeclLoopState arch source programs) with memory := memory} = (some (.result [.word value]),loopPost))
    (bound : let decls := compileTopExactHOL (fs.map DeclHOL.function) start
      let programs := compileProgDeclsHOLW decls
      let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
      let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
      let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
      LoopSteps.steps (optimiseHOL (compileHOLExact ctxt .ln (compileProgExactHOLW pan p)))
        {(concreteDeclLoopState arch source programs) with memory := memory} ≤ limit) :
    let programs := compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)
    let words := loopToWordCompileHOL (compileProgHOLExact arch programs)
    let starter := {(phase3Starter arch source programs template heapLength firstLoopName frame) with memory := memory}
    let state := {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac words).2}
    ∃ post, WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none) state =
      (some (.result (.loc 1 0) [.word value]),post) ∧ post.ffi = loopPost.ffi ∧
      WordSteps.steps (.call none (some firstLoopName) [0] none) state ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac words).2)) * (6*limit+1) := by
  let decls := compileTopExactHOL (fs.map DeclHOL.function) start
  let programs := compileProgDeclsHOLW decls
  let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0 (getEidsFromDeclsHOL decls)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) [])
  let crep := compileProgExactHOLW pan p
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let loopBody := optimiseHOL (compileHOLExact ctxt .ln crep)
  let loops := compileProgHOLExact arch programs
  let words := loopToWordCompileHOL loops
  let loop := {(concreteDeclLoopState arch source programs) with memory := memory}
  let starter := {(phase3Starter arch source programs template heapLength firstLoopName frame) with memory := memory}
  let wordCtxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
    (sptDifference (accVarsHOL loopBody .ln) (LoopToWord.toNumSetHOL []))) .ln
  have starterFacts := phase3Starter_relations arch source programs template heapLength firstLoopName frame memory heap
  have localFacts := phase3Starter_locals arch source programs template heapLength firstLoopName frame loopBody memory
  have entryMember : (firstLoopName,1,(LoopToWord.compHOL wordCtxt loopBody (firstLoopName,2)).1) ∈ words := by
    change (firstLoopName,1,loopToWordCompFuncHOL firstLoopName [] loopBody) ∈ words
    exact functionOnly_wordEntry fs start body found noInline arch
  have nodup : (words.map Prod.fst).Nodup := by
    simpa [words,loopToWordCompileHOL,loopToWordCompileProgHOL,List.map_map,Function.comp_def] using
      (firstCompileProgAllDistinctExact arch programs)
  have shapeTable := functionOnly_callFrontend_shapes fs start body .one found shapes
  have table : LoopTableSupported loop.code := callFrontend_declaration_loopTableSupported arch decls noInline shapeTable
  have panShape : CallFrontend pan p := .seq (.base .skip) (.tail (by simp))
  have loopShape : SimpleLoopSequenceSource loopBody :=
    optimise_simpleSequence (callFrontend_compiled_loopShape panShape ctxt .ln)
  have premises :
    let word := WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)]
      (sptLookup firstLoopName starter.stackSize) (WordSemStateFiniteExact.decClock starter)
    evaluate loopBody loop = (some (.result [.word value]),loopPost) ∧
    (some (.result [.word value]) : Option (LoopResultExact 64)) ≠ some .error ∧
    loopToWordStateRelHOLExact loop word ∧ LoopToWord.localsRelHOL wordCtxt loop.locals word.locals ∧
    sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
    (∀ k, sptMem k (accVarsHOL loopBody .ln) → sptMem k wordCtxt) := by
    refine ⟨run,by simp,starterFacts.1,localFacts.1,localFacts.2.1,?_,by decide,localFacts.2.2⟩
    exact Or.inr rfl
  have span := loopTable_wholeWord_span loopShape loop loopPost
    (some (.result [.word value])) table firstLoopName starter wordCtxt (firstLoopName,2) limit words wc ac entryMember nodup
    (loopToWord_programSafety loops) rfl starterFacts.2.1 starterFacts.2.2.1 starterFacts.2.2.2
    premises (.return [.word value]) bound
  obtain ⟨wordPost,wordResult,relation,result,ffi,visits⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  let state := {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac words).2}
  refine ⟨(WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none) state).2,?_,ffi,?_⟩
  · exact Prod.ext (by simpa [state,relation.2.1] using result) rfl
  · simpa [state,starter,words,loops] using visits

/-- Optimize a completed call-aware Loop entry using its explicit source visit limit. -/
theorem callFrontend_optimizedLoop {σ : Type} (pan : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : CallFrontend pan p) (ctxt : CrepToLoopContextExact)
    (source final : LoopSemStateFiniteExact 64 σ) (value : BitVec 64) (limit : Nat)
    (table : LoopTableSupported source.code)
    (run : evaluate (compileHOLExact ctxt .ln (compileProgExactHOLW pan p)) source =
      (some (.result [.word value]),final))
    (bound : LoopSteps.steps (compileHOLExact ctxt .ln (compileProgExactHOLW pan p)) source ≤ limit) :
    let body := compileHOLExact ctxt .ln (compileProgExactHOLW pan p)
    let opt := optimiseHOL body
    let factor := max (loopVisitWeight opt) (loopCodeWeight source.code+2)
    evaluate opt source = (some (.result [.word value]),final) ∧
    LoopSteps.steps opt source ≤ loopVisitWeight opt + factor * (2 * limit) := by
  let body := compileHOLExact ctxt .ln (compileProgExactHOLW pan p)
  let opt := optimiseHOL body
  let factor := max (loopVisitWeight opt) (loopCodeWeight source.code+2)
  have bodyShape : SimpleLoopSequenceSource body := callFrontend_compiled_loopShape shape ctxt .ln
  have optRun : evaluate opt source = (some (.result [.word value]),final) := by
    apply optimise_correct
    exact ⟨run,by simp,by simp,by simp,by simp⟩
  have optBound := simpleSequence_global_bound opt source factor (optimise_simpleSequence bodyShape)
    table (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have used := simpleSequence_global_consumed body source bodyShape table
  rw [optRun] at optBound
  rw [run] at used
  exact ⟨optRun,optBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left factor (used.trans (Nat.mul_le_mul_left 2 bound))) _)⟩

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- Counted source execution reaches the generated Loop entry with an explicit bound. -/
theorem countedCalls_functionOnlyLoop {scope : List VarName} {program : Prog (RiscV.Word 64)}
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
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (unique : ((functionsHOL (fs.map DeclHOL.function)).map Prod.fst).Nodup)
    (shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ body : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (Flapjack.Basis.Pure.MlString.ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL body ∧ CallSupportedIn names body ∧ ProgByteRanged body)
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
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
    (budget : count ≤ source.clock) (arch : AsmArchitecture) (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact source.memory memory source.memaddrs) :
    let decls := fs.map DeclHOL.function
    let lowered := compileTopExactHOL decls start
    let renamed := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
    let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
    let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
    let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
    let programs := compileProgDeclsHOLW lowered
    let crep := compileProgExactHOLW pan p
    let initial := concreteDeclCrepState before programs
    let loop := {(concreteDeclLoopState arch initial programs) with memory := memory}
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) *
      (1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2)
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let budget := callClockFactor ctxt rows initial.clock crep * (limit+1)
    let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
    let loopLimit := callSyntaxCost ctxt crep + factor * (initial.clock+budget)
    let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
    let optFactor := max (loopVisitWeight opt) (loopCodeWeight loop.code+2)
    ∃ (sourceFinal lowerFinal : PanSemStateFiniteExact 64 σ) (post : LoopSemStateFiniteExact 64 σ),
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      before.evaluateHOLFiniteState p = (some (.returned (.val (.word value))),emptyLocalsHOLFinite lowerFinal) ∧
      evaluate (compileHOLExact ctxt .ln crep) {loop with clock := loop.clock+budget} = (some (.result [.word value]),post) ∧
      LoopSteps.steps (compileHOLExact ctxt .ln crep) {loop with clock := loop.clock+budget} ≤
        callSyntaxCost ctxt crep + factor * (initial.clock+budget) ∧
      evaluate opt {loop with clock := loop.clock+budget} = (some (.result [.word value]),post) ∧
      LoopSteps.steps opt {loop with clock := loop.clock+budget} ≤ loopVisitWeight opt + optFactor * (2 * loopLimit) ∧
      post.ffi = lowerFinal.ffi ∧ lowerFinal.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  obtain ⟨sourceFinal,lowerFinal,crepFinal,sourceRun,lowerRun,crepRun,crepBound,crepFfi,lowerFfi,ffiRel⟩ :=
    countedCalls_functionOnlyCrep supported production source rel ranged words byteRanged codeRanged codeShape
      targetCode codeRel entries sourceCode entryShapes fs start targetTable found mainFound locals globals structs
      exceptions unique shapes noInline topOutside aligned context primitive handler exnContracts fuel count
      postLocals postGlobals postMemory postFfi value run budget
  have span := functionOnlyCrep_toLoop fs start (progToHOL (panSimpProg program)) found unique shapes noInline
    _ crepFinal value _ rfl rfl arch memory (by simpa [concreteDeclCrepState,noGlobalsLoweredPreCall] using memoryRel) rfl crepRun crepBound
  obtain ⟨post,loopRun,loopFfi,loopBound⟩ := span
  let decls := fs.map DeclHOL.function
  let lowered := compileTopExactHOL decls start
  let programs := compileProgDeclsHOLW lowered
  let renamed : PanSemStateFiniteExact 64 σ := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
  let initial := concreteDeclCrepState before programs
  let loop := {(concreteDeclLoopState arch initial programs) with memory := memory}
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let crep := compileProgExactHOLW pan p
  let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) *
    (1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2)
  let rows := programs.map (fun row => (row.2.1,row.2.2))
  let extra := callClockFactor ctxt rows initial.clock crep * (limit+1)
  let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
  have panShape : CallFrontend pan p := .seq (.base .skip) (.tail (by simp))
  have shapeTable := functionOnly_callFrontend_shapes fs start (progToHOL (panSimpProg program)) .one found shapes
  have table : LoopTableSupported {loop with clock := loop.clock+extra}.code :=
    callFrontend_declaration_loopTableSupported arch lowered noInline shapeTable
  have opt := callFrontend_optimizedLoop pan p panShape ctxt {loop with clock := loop.clock+extra} post value
    (callSyntaxCost ctxt crep + factor * (initial.clock+extra)) table loopRun loopBound
  exact ⟨sourceFinal,lowerFinal,post,sourceRun,lowerRun,loopRun,loopBound,opt.1,opt.2,
    loopFfi.trans crepFfi,lowerFfi,ffiRel⟩

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- A counted original source return reaches the generated optimized Word start with an explicit bound. -/
theorem countedCalls_functionOnlyWord {C : Type} {scope : List VarName} {program : Prog (RiscV.Word 64)}
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
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (unique : ((functionsHOL (fs.map DeclHOL.function)).map Prod.fst).Nodup)
    (shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ body : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (Flapjack.Basis.Pure.MlString.ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL body ∧ CallSupportedIn names body ∧ ProgByteRanged body)
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
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
    (budget : count ≤ source.clock) (arch : AsmArchitecture) (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact source.memory memory source.memaddrs)
    (template : WordSemStateFiniteExact 64 C σ) (heapLength : BitVec 64) (frame : Nat)
    (wc : Config) (ac : AsmConfigExact 64)
    (heap : source.topAddr = source.baseAddr + 2 * heapLength) :
    let decls := fs.map DeclHOL.function
    let lowered := compileTopExactHOL decls start
    let renamed := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
    let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
    let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
    let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
    let programs := compileProgDeclsHOLW lowered
    let crep := compileProgExactHOLW pan p
    let initial := concreteDeclCrepState before programs
    let loop := {(concreteDeclLoopState arch initial programs) with memory := memory}
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let crepLimit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) *
      (1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2)
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let extra := callClockFactor ctxt rows initial.clock crep * (crepLimit+1)
    let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
    let loopLimit := callSyntaxCost ctxt crep + factor * (initial.clock+extra)
    let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
    let optFactor := max (loopVisitWeight opt) (loopCodeWeight loop.code+2)
    let optLimit := loopVisitWeight opt + optFactor * (2 * loopLimit)
    let replay := {initial with clock := loop.clock+extra}
    let words := loopToWordCompileHOL (compileProgHOLExact arch programs)
    let starter := {(phase3Starter arch replay programs template heapLength firstLoopName frame) with memory := memory}
    let word := {starter with clock := 6*optLimit+1, code := sptFromAList (compile wc ac words).2}
    ∃ (sourceFinal : PanSemStateFiniteExact 64 σ) (post : WordSemStateFiniteExact 64 C σ),
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none) word =
        (some (.result (.loc 1 0) [.word value]),post) ∧
      WordSteps.steps (.call none (some firstLoopName) [0] none) word ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac words).2)) * (6*optLimit+1) ∧
      post.ffi = sourceFinal.ffi ∧ FfiStateRel postFfi sourceFinal.ffi := by
  obtain ⟨sourceFinal,lowerFinal,loopPost,sourceRun,_,_,_,optRun,optBound,loopFfi,lowerFfi,ffiRel⟩ :=
    countedCalls_functionOnlyLoop supported production source rel ranged words byteRanged codeRanged codeShape
      targetCode codeRel entries sourceCode entryShapes fs start targetTable found mainFound locals globals structs
      exceptions unique shapes noInline topOutside aligned context primitive handler exnContracts fuel count
      postLocals postGlobals postMemory postFfi value run budget arch memory memoryRel
  let decls := fs.map DeclHOL.function
  let lowered := compileTopExactHOL decls start
  let programs := compileProgDeclsHOLW lowered
  let renamed : PanSemStateFiniteExact 64 σ := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let pan := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
  let initial := concreteDeclCrepState before programs
  let loop := {(concreteDeclLoopState arch initial programs) with memory := memory}
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let crep := compileProgExactHOLW pan p
  let limit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) *
    (1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2)
  let rows := programs.map (fun row => (row.2.1,row.2.2))
  let extra := callClockFactor ctxt rows initial.clock crep * (limit+1)
  let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
  let loopLimit := callSyntaxCost ctxt crep + factor * (initial.clock+extra)
  let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
  let optFactor := max (loopVisitWeight opt) (loopCodeWeight loop.code+2)
  let optLimit := loopVisitWeight opt + optFactor * (2*loopLimit)
  let replay := {initial with clock := loop.clock+extra}
  have replayHeap : replay.topAddr = replay.baseAddr + 2 * heapLength := by
    simpa [replay,initial,concreteDeclCrepState,before,noGlobalsLoweredPreCall,renamed] using heap
  have loopEq : {(concreteDeclLoopState arch replay programs) with memory := memory} =
      {loop with clock := loop.clock+extra} := by
    simp [loop,replay,concreteDeclLoopState]
  have span := functionOnly_optimizedWord fs start (progToHOL (panSimpProg program)) found shapes noInline arch
    replay template heapLength frame wc ac memory optLimit value loopPost replayHeap
    (by
      change evaluate opt {(concreteDeclLoopState arch replay programs) with memory := memory} = _
      rw [loopEq]
      exact optRun)
    (by
      change LoopSteps.steps opt {(concreteDeclLoopState arch replay programs) with memory := memory} ≤ optLimit
      rw [loopEq]
      exact optBound)
  obtain ⟨post,wordRun,wordFfi,wordBound⟩ := span
  exact ⟨sourceFinal,post,sourceRun,wordRun,wordBound,wordFfi.trans (loopFfi.trans lowerFfi),ffiRel⟩

/-- Every counted supported run, including errors, reaches the actual
simplified and global-lowered callee with the same source result. -/
theorem supported_counted_frontend_prefix {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
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
    (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
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
    (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
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

end SteppedFlapjack.Concrete
