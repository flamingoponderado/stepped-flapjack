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
        3 + CrepSteps.statementWeight (compileProgExactHOLW callee body) * (1 + 1 + programWeight program) := by
  let program : Prog (RiscV.Word 64) := .skip
  let source := clockedFixtureSource program 1
  let production := clockedFixtureProduction program 1
  let _ : DecidablePred source.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have supported : Supported program := ⟨.skip, by simp [program,ProgByteRanged]⟩
  obtain ⟨rel,ranged,words⟩ := clockedFixture_premises program 1
  have run : evalPanValueFfiProgSteps context primitive handler production.structs [] production.baseAddress production.topAddress
      panSemBitVec64BytesInWord 1 production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal production.locals production.globals production.memory production.ffi,1) := by
    simp [program,evalPanValueFfiProgSteps]
  obtain ⟨exit,final,outcome,target,bound⟩ := supported_counted_full_frontend_exit program supported production source rel ranged words
    rfl rfl rfl rfl context primitive handler [] 1 1 1 _ run (by omega) rfl
  cases outcome with
  | normal l g m f =>
    simp only [countedFrontendFactor,countedErrorBonus,Nat.mul_zero,Nat.add_zero,Nat.one_mul] at bound
    exact ⟨final,target,bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.min_le_left _ _)) 3)⟩
end SteppedFlapjack.Concrete
