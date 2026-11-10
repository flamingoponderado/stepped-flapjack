import SteppedFlapjack.Concrete.Phase7Frontend
import SteppedFlapjack.Concrete.CountdownWordSpan

/-! Code-derived supported source to optimized Word composition. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps

/-- The Loop clock allowance calculated from the generated callee. -/
def supportedLoopBudget (program : Prog (RiscV.Word 64)) (n : Nat) : Nat :=
  let body := progToHOL (panSimpProg program)
  let ctxt := witnessLoopContext riscvConfig.isa body
  let code := compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln (supportedCallee body)
  3 * loopVisitWeight (optimiseHOL code) * (supportedCrepBudget program n + 1)

def supportedLoopVisits (program : Prog (RiscV.Word 64)) (n : Nat) : Nat :=
  let body := progToHOL (panSimpProg program)
  let ctxt := witnessLoopContext riscvConfig.isa body
  let code := compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln (supportedCallee body)
  loopVisitWeight (optimiseHOL code) * (supportedCrepBudget program n + supportedLoopBudget program n + 1) + 8

def supportedWordBound (program : Prog (RiscV.Word 64)) (n : Nat) : Nat :=
  let body := progToHOL (panSimpProg program)
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName body) (supportedCallee body)
    (supportedLoopVisits program n) phase3WordConfig riscvConfig

set_option maxHeartbeats 1000000 in
/-- A counted supported return reaches the optimized Word entry at a bound
calculated from the generated code and the concrete source visit budget. -/
theorem supported_counted_word {C : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (fuel count n : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (word : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL program)).structs []
      (executableState (progToHOL program)).baseAddress (executableState (progToHOL program)).topAddress
      panSemBitVec64BytesInWord fuel (executableState (progToHOL program)).locals
      (executableState (progToHOL program)).globals (executableState (progToHOL program)).memory
      (executableState (progToHOL program)).ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL program)))) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count)) (countBound : count ≤ n)
    (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact
      (crepStateFrom (panSimpSourceState program (clockedFixtureSource program (n+1))) (progToHOL (panSimpProg program))).memory memory
      (crepStateFrom (panSimpSourceState program (clockedFixtureSource program (n+1))) (progToHOL (panSimpProg program))).memaddrs)
    (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :
    let simple := panSimpProg program
    let body := progToHOL simple
    let pan := panSimpSourceState program (clockedFixtureSource program (n+1))
    let crep := crepStateFrom pan body
    let timed := {crep with clock := crep.clock + supportedLoopBudget program n}
    let code := crepPrograms body
    let words := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa code)
    let starter := {(phase3Starter riscvConfig.isa timed code template fixtureHeapLength 64 frame) with memory := memory}
    let state := {starter with clock := 6 * supportedLoopVisits program n + 1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig words).2}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep (.seq .skip (.call none (entryName body) [])) = (some (.return [.word word]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word word]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none) state ≤ supportedWordBound program n ∧
      FfiStateRel postFfi final.ffi := by
  let simple := panSimpProg program
  let body := progToHOL simple
  let pan := panSimpSourceState program (clockedFixtureSource program (n+1))
  let crep := crepStateFrom pan body
  let timed := {crep with clock := crep.clock + supportedLoopBudget program n}
  let code := crepPrograms body
  have shape := supportedCallee_scalar simple (supported_panSimp program supported).1
  have codeEq : code = twoPrograms (ofString "main") (entryName body) (supportedCallee body) :=
    supported_crepPrograms simple (supported_panSimp program supported).1
  obtain ⟨final,post,crepRun,_,loopRun,loopBound,stateRel,_,_,_,crepFfi⟩ :=
    supported_counted_loop riscvConfig.isa program supported context primitive handler fuel count n
      postLocals postGlobals postMemory postFfi word run countBound memory memoryRel
  have heap : timed.topAddr = timed.baseAddr + 2*fixtureHeapLength := by
    simpa [timed,crep,pan] using fixture_heap program (n+1) body
  have loopEq : concreteDeclLoopState riscvConfig.isa timed code =
      {loopStateFrom riscvConfig.isa pan body with clock :=
        (loopStateFrom riscvConfig.isa pan body).clock + supportedLoopBudget program n} := by
    simp [timed,crep,pan,code,loopStateFrom,concreteDeclLoopState]
  have sourceRun : evaluate branchingLoopEntry {(concreteDeclLoopState riscvConfig.isa timed code) with memory := memory} =
      (some (.result [.word word]),post) := by
    rw [loopEq]
    simpa [pan,body,simple,supportedLoopBudget] using loopRun
  have sourceBound : LoopSteps.steps branchingLoopEntry {(concreteDeclLoopState riscvConfig.isa timed code) with memory := memory} ≤
      supportedLoopVisits program n := by
    rw [loopEq]
    simpa [pan,body,simple,supportedLoopBudget,supportedLoopVisits] using loopBound
  have span := twoProgram_wholeWord_span riscvConfig.isa (ofString "main") (entryName body)
    (supportedCallee body) (Ne.symm (entryName_fresh body)) shape timed post [.word word]
    (supportedLoopVisits program n) template fixtureHeapLength frame countdownRiscVBackend.wordToWordConf riscvConfig
    memory heap
    (by rw [← codeEq]; exact sourceRun) (by rw [← codeEq]; exact sourceBound)
  obtain ⟨_,wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  refine ⟨final,post,crepRun,stateRel,?_,?_,?_,crepFfi⟩
  · simpa only [← codeEq,relation.2.1] using result
  · simpa only [← codeEq] using ffi
  · simpa only [supportedWordBound,phase3WordConfig_eq,← codeEq] using bound
end SteppedFlapjack.Concrete
