import SteppedFlapjack.Concrete.GlobalCountedMachine
import SteppedFlapjack.Concrete.FunctionSource
import SteppedFlapjack.Concrete.Phase7Frontend
import SteppedFlapjack.Concrete.Phase7NativeFacts
import SteppedFlapjack.Concrete.Phase7SourceBehaviour
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.CrepToLoopSteps
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def singletonFunctions (p : Prog (RiscV.Word 64)) : List (FunDeclOf 64) := [⟨"main",false,false,[],p,.one⟩]
def singletonSourceProgram (p : Prog (RiscV.Word 64)) : List (DeclHOL 64) :=
  ((singletonFunctions p).map funDeclToHOL).map DeclHOL.function
private theorem tableSupported (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) : FunctionTableSupported (singletonFunctions p) := by
  intro f hf
  simp only [singletonFunctions,List.mem_cons,List.not_mem_nil,or_false] at hf
  subst f
  refine ⟨?_,(CallSupportedIn.base h.1),?_,rfl⟩
  · simp [FunDeclByteRanged,ListParamByteRanged,ShapeByteRanged,NameRanged,h.2]
  · simp
private theorem declsEq (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    globalCompilerDecls (singletonSourceProgram p) = compileTopExactHOL (declarations (progToHOL (panSimpProg p))) (ofString "main") := by
  unfold globalCompilerDecls singletonSourceProgram
  rw [simpFunctions]
  rw [call_structs_top (singletonFunctions p) (tableSupported p h)]
  have body := callSupported_panSimp_hol (CallSupportedIn.base h.1)
  simp [singletonFunctions,funDeclToHOL,declarations,singleEntryProgram,body,shapeToHOL]
/-- The actual compiler uses the normalized singleton frontend table. -/
theorem singleton_programs (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    globalSourcePrograms (singletonSourceProgram p) = crepPrograms (progToHOL (panSimpProg p)) := by
  change compileProgDeclsHOLW (globalCompilerDecls (singletonSourceProgram p)) = _
  rw [declsEq p h]
  rfl
/-- The actual compiler outputs for a singleton agree with the supported frontend. -/
theorem singleton_raw (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    globalSourceRaw (singletonSourceProgram p) = supportedWordPrograms p := by
  unfold globalSourceRaw supportedWordPrograms
  rw [singleton_programs p h]
theorem singleton_words (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    globalSourceWords (singletonSourceProgram p) = (supportedAllocated p).2 := by
  unfold globalSourceWords supportedAllocated
  rw [singleton_raw p h]
theorem singleton_native (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    globalSourceNative (singletonSourceProgram p) = supportedNative p := by
  unfold globalSourceNative supportedNative
  rw [singleton_words p h]
theorem singleton_bitmap (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    globalSourceBitmaps (singletonSourceProgram p) = [4] := by
  unfold globalSourceBitmaps
  rw [singleton_native p h]
  exact supported_native_bitmap p h
theorem singleton_safe (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (safe : fixtureStackSafe (supportedNative p).2.2.2 = true) : fixtureStackSafe (globalSourceCode (singletonSourceProgram p)) = true := by
  unfold globalSourceCode
  rw [singleton_native p h]
  exact safe
theorem singleton_facts (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (facts : (fixtureRemoveLabels (supportedNative p).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative p).2.2.2).length ≤ 0xecc ∧ (fixtureCodeBytes (supportedNative p).2.2.2).length % 4 = 0) :
    (fixtureRemoveLabels (globalSourceCode (singletonSourceProgram p))).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode (singletonSourceProgram p))).length ≤ 0xecc ∧
      (fixtureCodeBytes (globalSourceCode (singletonSourceProgram p))).length % 4 = 0 := by
  unfold globalSourceCode
  rw [singleton_native p h]
  exact facts
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
def singletonCapacity (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  let entry := ((sptLookup 64 (sptFromAList words)).getD (1,.skip)).2
  let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList words)
  optionLe (optionMap₂ max (some (max 1 (1+frame)))
    (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList words)))) (some 2097172)
theorem singleton_capacity (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (cap : singletonCapacity (supportedAllocated p).2) :
    optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame (singletonSourceProgram p))))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames (singletonSourceProgram p)) 64
        (sptFromAList (globalSourceWords (singletonSourceProgram p)))))) (some 2097172) := by
  change singletonCapacity (globalSourceWords (singletonSourceProgram p))
  rw [singleton_words p h]
  exact cap
def singletonName (p : Prog (RiscV.Word 64)) : MlS := entryName (progToHOL (panSimpProg p))
def singletonEntries (p : Prog (RiscV.Word 64)) : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  [(singletonName p,[],progToHOL (panSimpProg p),.one)]
def singletonGlobals : PanGlobalsContextExact 64 := beforeGlobalsContext 0

def singletonPost (bitmapWords clock : Nat) : PanSemStateFiniteExact 64 Unit :=
  {(sourceTemplateFor bitmapWords) with clock := clock+1}
private instance (bitmapWords clock : Nat) : DecidablePred (singletonPost bitmapWords clock).memaddrs := by
  change DecidablePred ordinaryAddress
  infer_instance
private instance (bitmapWords clock : Nat) : DecidablePred (singletonPost bitmapWords clock).shMemaddrs := by
  change DecidablePred sharedAddress
  infer_instance
private theorem entrySupported (p : Prog (RiscV.Word 64)) (bitmapWords clock : Nat) (h : CallFreeSupported p) :
    GlobalSupportedEntries (globalEntryShapes (singletonPost bitmapWords clock) (singletonEntries p)) (singletonEntries p) := by
  intro name params body ret found
  simp only [singletonEntries,List.lookup] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    exact ⟨[],panSimpProg p,rfl,rfl,GlobalCallSupportedIn.base (supported_panSimp p h).1.1,(supported_panSimp p h).1.2⟩
  · simp at found
private theorem allRows (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    functionsHOL (globalCompilerDecls (singletonSourceProgram p)) =
      (ofString "main",[],.seq (nestedSeqHOL []) (.call none (singletonName p) []),.one) ::
        (singletonEntries p).map (fun e => (e.1,e.2.1,compileProgExactHOL singletonGlobals e.2.2.1,e.2.2.2)) := by
  rw [declsEq p h,lowered_declarations]
  have hs := (supported_panSimp p h).1
  have rename := supported_fperm hs (ofString "main") (singletonName p)
  have global := supported_globals_fixed hs singletonGlobals
  have globalEmpty := supported_globals_fixed hs emptyGlobalsContext
  simp only [singletonName] at rename
  simp [functionsHOL,singletonEntries,singletonName,nestedSeqHOL,rename,global,globalEmpty]
private theorem noInline (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    (functionsHOL ((globalCompilerDecls (singletonSourceProgram p)).filter inlinableHOL)).map Prod.fst = [] := by
  rw [declsEq p h]
  exact singleEntry_inline_selection_empty _ _
private theorem exceptionsEmpty (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p) :
    (globalCompilerContext (singletonSourceProgram p)).eids = HolFiniteMapExact.empty := by
  unfold globalCompilerContext
  rw [declsEq p h]
  simp [declarations,singleEntry_compiled_eids_empty,mkCtxtExactHOL]
private theorem addressEmpty (a : BitVec 64) : ¬ addresses heapTop 0 a := by
  rw [mem_addresses]
  simp
private theorem beforeEq (p : Prog (RiscV.Word 64)) (bitmapWords clock : Nat)
    (bitmapLength : bitmapWords = (globalSourceBitmaps (singletonSourceProgram p)).length) :
    beforeGlobals (globalEntryTarget (singletonSourceProgram p) clock singletonGlobals (singletonEntries p)) 0 0 = singletonPost bitmapWords clock := by
  have domain : (fun a => ordinaryAddress a ∧ ¬ addresses heapTop 0 a) = ordinaryAddress := by
    funext a
    exact propext (by simp [addressEmpty])
  simp [singletonPost,globalEntryTarget,installTargetFunctions,globalEntryTemplate,beforeGlobals,
    sourceTemplateFor,sourceTemplate,domain,bitmapLength]
private theorem allocatedEmpty (source : List (DeclHOL 64)) (clock : Nat) : ∀ a, addresses ((globalEntryTemplate source clock).topAddr - panBytesInWord 64 *
      BitVec.ofNat 64 ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum)
      ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum a → (globalEntryTemplate source clock).memaddrs a := by
  intro a present
  rw [mem_addresses] at present
  obtain ⟨i,hi,_⟩ := present
  simp [decShapesHOL] at hi

noncomputable def singletonTicks (p : Prog (RiscV.Word 64)) (bitmapWords clock : Nat) : Nat :=
  initializedGlobalTicks (singletonSourceProgram p) clock [] (singletonPost bitmapWords clock) [] singletonGlobals
    (singletonEntries p) (singletonName p) (globalCompilerContext (singletonSourceProgram p))
/-- A call-free function source reaches its initialized machine at a code-derived clock. -/
theorem singleton_counted_machine (p : Prog (RiscV.Word 64)) (supported : CallFreeSupported p) (bitmapWords clock : Nat)
    (bitmapLength : bitmapWords = (globalSourceBitmaps (singletonSourceProgram p)).length)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (exceptions : InfoMap Shape)
    (fuel count : Nat) (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).structs
      (countedFunctionsOfCode (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).code)
      (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).baseAddress
      (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).topAddress panSemBitVec64BytesInWord fuel
      (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).locals (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).globals
      (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).memory (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).ffi (panSimpProg p)
      (memoryAccess := some (panSemBitVec64MemoryAccess (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p))))
      (contracts := some (countedContractsOfCode (globalEntryProduction (singletonPost bitmapWords clock) (singletonEntries p)).code exceptions)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ clock)
    (bitmapFits : 0xa0020018 + (globalSourceBitmaps (singletonSourceProgram p)).length*8 ≤ 0xa0410000)
    (safe : fixtureStackSafe (globalSourceCode (singletonSourceProgram p)) = true)
    (facts : (fixtureRemoveLabels (globalSourceCode (singletonSourceProgram p))).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode (singletonSourceProgram p))).length ≤ 0xecc ∧ (fixtureCodeBytes (globalSourceCode (singletonSourceProgram p))).length % 4 = 0)
    (capacity : optionLe
      (optionMap₂ max (some (max 1 (1 + globalSourceFrame (singletonSourceProgram p))))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames (singletonSourceProgram p)) 64
          (sptFromAList (globalSourceWords (singletonSourceProgram p)))))) (some 2097172)) :
    ∃ sourceFinal : PanSemStateFiniteExact 64 Unit, ∃ finalMachine finalFfi compilerFinal,
      Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram p) =
        some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram p)),globalSourceBitmaps (singletonSourceProgram p),compilerFinal) ∧
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram p)))) sourceFfi
        (singletonTicks p bitmapWords clock) (configuredMachineState (globalSourceCode (singletonSourceProgram p)) (globalSourceBitmaps (singletonSourceProgram p))) =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel postFfi sourceFinal.ffi := by
  have unique : ((functionsHOL (singletonSourceProgram p)).map Prod.fst).Nodup := by
    simp [singletonSourceProgram,singletonFunctions,funDeclToHOL,functionsHOL]
  have good : pancakeGoodCodeHOL (singletonSourceProgram p) = true := table_good (singletonFunctions p) (tableSupported p supported)
  have eval : @evaluateDeclsHOLFinite 64 Unit _
      (beforeGlobals (globalEntryTarget (singletonSourceProgram p) clock singletonGlobals (singletonEntries p)) 0 0)
      (fun _ => Classical.propDecidable _) [] = some (singletonPost bitmapWords clock) := by
    change some (beforeGlobals (globalEntryTarget (singletonSourceProgram p) clock singletonGlobals (singletonEntries p)) 0 0) = _
    rw [beforeEq p bitmapWords clock bitmapLength]
  have allocated := allocatedEmpty (singletonSourceProgram p) clock
  have h := initializedGlobal_counted_machine (singletonSourceProgram p) unique good clock [] (singletonPost bitmapWords clock) [] [] [] singletonGlobals
    (singletonEntries p) (singletonName p) (panSimpProg p)
    ⟨GlobalCallSupportedIn.base (supported_panSimp p supported).1.1,(supported_panSimp p supported).1.2⟩ value
    (by simp) (by simp) eval (by simp [compileDecsExactHOL,singletonGlobals,beforeGlobalsContext,decShapesHOL]) allocated (by decide)
    (by simp [singletonEntries]) (entrySupported p bitmapWords clock supported)
    context primitive handler exceptions fuel count postLocals postGlobals postMemory postFfi run (by simpa [singletonPost,callEntryStateHOLFinite,installSourceFunctions,decClockHOLFinite] using budget)
    (allRows p supported) (noInline p supported) (exceptionsEmpty p supported) bitmapFits safe facts capacity
  exact h
private instance (fs : List (FunDeclOf 64)) (bitmapWords clock : Nat) :
    DecidablePred (functionSourceExact fs bitmapWords clock).memaddrs := by
  change DecidablePred ordinaryAddress
  infer_instance
/-- A counted run of the original singleton body determines its declaration semantics. -/
theorem singleton_source_semantics (p : Prog (RiscV.Word 64)) (supported : CallFreeSupported p)
    (bitmapWords clock : Nat)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (exceptions : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (value : BitVec 64)
    (run : let production := functionSourceProduction (singletonFunctions p) bitmapWords clock
      evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi p
        (memoryAccess := some (panSemBitVec64MemoryAccess production))
        (contracts := some (countedContractsOfCode production.code exceptions)) =
          some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ clock) :
    ∃ final : PanSemStateFiniteExact 64 Unit,
      (functionSourceExact (singletonFunctions p) bitmapWords clock).evaluateHOLFiniteState (progToHOL p) =
        (some (.returned (.val (.word value))),final) ∧
      semanticsDecls {(sourceTemplateFor bitmapWords) with clock := 0} (ofString "main") (singletonSourceProgram p) =
        .terminate .success final.ffi.ioEvents ∧ FfiStateRel postFfi final.ffi := by
  let production := functionSourceProduction (singletonFunctions p) bitmapWords clock
  let source := functionSourceExact (singletonFunctions p) bitmapWords clock
  have table := tableSupported p supported
  have related : PanSemStateRelExec production source.toExact :=
    functionSource_related (singletonFunctions p) bitmapWords clock (table_names _ table)
  have ranged : PanSemStateRelExecRanged production := by
    simp [production,functionSourceProduction,sourceProduction,PanSemStateRelExecRanged,StructContextByteRanged,StructContext.toHOL]
  have words : WordLocals production.locals := wordLocals_empty
  have codeRanged := table_code_ranged (singletonFunctions p) bitmapWords clock table
  have codeShape := table_counted_shapes (singletonFunctions p) bitmapWords clock table
  obtain ⟨holResult,final,holRun,outcome,_,_⟩ := supportedCalls_counted_source (.base supported.1)
    production source related ranged words supported.2 codeRanged codeShape context primitive handler exceptions fuel count _ run (by simpa [source,functionSourceExact] using budget)
  cases outcome with
  | returned locals globals memory ffi word final nextRel nextRanged nextWords =>
    have wf : ((singletonFunctions p).map funDeclToHOL).all (fun f => f.params.all (fun q => isWfShapeExactHOL ([] : StructContextExact) q.2) &&
        isWfShapeExactHOL ([] : StructContextExact) f.returnShape) = true := table_wellFormed _ table
    have unique : ((functionsHOL (singletonSourceProgram p)).map Prod.fst).Nodup := by
      simp [singletonSourceProgram,singletonFunctions,funDeclToHOL,functionsHOL]
    have found : (functionsHOL (singletonSourceProgram p)).lookup (ofString "main") = some ([],progToHOL p,.one) := by
      simp [singletonSourceProgram,singletonFunctions,funDeclToHOL,functionsHOL,shapeToHOL]
    have initialEq : ({(sourceTemplateFor bitmapWords) with structs := [], code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (singletonSourceProgram p)).reverse), clock := clock} : PanSemStateFiniteExact 64 Unit) = source := by
      simp [source,functionSourceExact,singletonSourceProgram,sourceTemplateFor,sourceTemplate,List.map_map,Function.comp_def]
    have run' : (let declared := {(sourceTemplateFor bitmapWords) with clock := 0, structs := [], code :=
          (HolFiniteMapExact.empty.updateList (functionsHOL (singletonSourceProgram p)).reverse)}
        ({declared with clock := clock} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState (progToHOL p)) =
          (some (.returned (.val (.word value))),final) := by
      change ({(sourceTemplateFor bitmapWords) with structs := [], code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (singletonSourceProgram p)).reverse), clock := clock} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState (progToHOL p) = _
      rw [initialEq]
      exact holRun
    have behavior := functionOnly_body_semantics {(sourceTemplateFor bitmapWords) with clock := 0} (ofString "main")
      ((singletonFunctions p).map funDeclToHOL) (progToHOL p) wf unique rfl rfl found clock final value run' 
    exact ⟨final,holRun,behavior,nextRel.2.2.2.2.2.2.2.2.2.2.1⟩
end SteppedFlapjack.Concrete
