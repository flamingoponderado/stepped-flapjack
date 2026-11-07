import SteppedFlapjack.Concrete.CountedApplications
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let program : Prog (RiscV.Word 64) := .skip
    let source := clockedFixtureSource program 1
    let body := progToHOL (panSimpProg program)
    let callee := ctxtFcExactHOL (frontendContext body).funcs (frontendContext body).eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ final,
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program source) body) entry = (some .error,final) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program source) body) ≤
        3 + sizeOf (compileProgExactHOLW callee body) * (sizeOf (compileProgExactHOLW callee body) * 2) := by
  let program : Prog (RiscV.Word 64) := .skip
  let source := clockedFixtureSource program 1
  let production := clockedFixtureProduction program 1
  let _ : DecidablePred source.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have supported : Supported program := ⟨.skip, by simp [program,ProgByteRanged]⟩
  have rel : PanSemStateRelExec production source.toExact := by
    obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := source_related (progToHOL program)
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  have ranged : PanSemStateRelExecRanged production :=
    PanSemStateRelExecRanged.setClock (source_ranged (progToHOL program)) 1
  have words : WordLocals production.locals := by
    intro name value found
    simp [production,clockedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction] at found
  have topOutside : ¬ source.memaddrs source.topAddr := by
    simp [source,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate,ordinaryAddress,heapTop,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  have aligned : panGlobalsByteAlignedHOL source.topAddr := by
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  have run : evalPanValueFfiProgSteps context primitive handler production.structs [] production.baseAddress production.topAddress
      panSemBitVec64BytesInWord 1 production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal production.locals production.globals production.memory production.ffi,1) := by
    simp [program,evalPanValueFfiProgSteps]
  obtain ⟨exit,final,outcome,target,bound⟩ := supported_counted_full_frontend_exit program supported production source rel ranged words
    rfl rfl rfl rfl topOutside aligned rfl context primitive handler [] 1 1 1 _ run (by trivial) (by omega) rfl
  cases outcome with
  | normal l g m f => exact ⟨final,target,bound⟩
end SteppedFlapjack.Concrete
