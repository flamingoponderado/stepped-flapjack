import SteppedFlapjack.Concrete.GlobalStructCrep
import SteppedFlapjack.CrepToLoopSteps.ScalarSequenceBound
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

def globalStructCrepProgram : CrepProgHOL 64 :=
  compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))

theorem globalStruct_scalar_program : ScalarProgram globalStructCrepProgram :=
  frontend_scalar_program globalStruct_frontend

def globalStructLoopContext : CrepToLoopContextExact :=
  mkCtxtExact riscvConfig.isa HolFiniteMapExact.empty HolFiniteMapExact.empty 0

noncomputable def globalStructLoopState : LoopSemStateFiniteExact 64 Unit :=
  concreteDeclLoopState riscvConfig.isa globalStructCrepState []

def globalStructLoopClock : Nat :=
  3 * loopVisitWeight (optimiseHOL (compileHOLExact globalStructLoopContext .ln globalStructCrepProgram)) * 11

/-- The concrete pair program reaches optimized Loop code at a calculated clock. -/
theorem globalStruct_loop_run : ∃ sourcePost targetPost crepPost loopPost,
    globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),sourcePost) ∧
    globalStructTarget.evaluateHOLFiniteState (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) =
      (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) ∧
    evalCrepSemHOLProgExact globalStructCrepState globalStructCrepProgram = (some (.return [.word 8]),crepPost) ∧
    LoopSemStateFiniteExact.evaluate (optimiseHOL (compileHOLExact globalStructLoopContext .ln globalStructCrepProgram))
      {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} =
        (resultToLoop (some (.return [.word 8])),loopPost) ∧
    SteppedFlapjack.LoopSteps.steps (optimiseHOL (compileHOLExact globalStructLoopContext .ln globalStructCrepProgram))
      {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} ≤
        loopVisitWeight (optimiseHOL (compileHOLExact globalStructLoopContext .ln globalStructCrepProgram)) *
          (10 + globalStructLoopClock + 1) := by
  obtain ⟨sourcePost,targetPost,crepPost,sourceRun,targetRun,crepRun,_,crepBound⟩ := globalStruct_crep_run
  have crepGlobals : globalStructCrepState.globals = HolFiniteMapExact.empty := rfl
  obtain ⟨stateRel,memRel,globalsRel⟩ := concreteDecl_crepLoop_relations riscvConfig.isa globalStructCrepState [] crepGlobals
  have codeRel : crepToLoopCodeRelExact globalStructLoopContext globalStructCrepState.code globalStructLoopState.code := by
    simp [crepToLoopCodeRelExact,crepToLoopDistinctFuncs,globalStructLoopContext,mkCtxtExact,
      globalStructCrepState,concreteDeclCrepState,alistToFmapCodeExact,HolFiniteMapExact.empty,FLOOKUP,FUPDATE_LIST]
  have localsRel : crepToLoopLocalsRelExact globalStructLoopContext .ln globalStructCrepState.locals globalStructLoopState.locals := by
    apply empty_crepLoop_locals
    rfl
  obtain ⟨loopPost,loopRun,loopBound,_,_,_,_⟩ := scalarProgram_explicit globalStructCrepProgram globalStruct_scalar_program
    globalStructLoopContext .ln globalStructCrepState crepPost (some (.return [.word 8])) globalStructLoopState 10
    (by simpa [globalStructCrepProgram] using crepRun) (by simpa [globalStructCrepProgram] using crepBound)
    (.return _) stateRel memRel globalsRel codeRel localsRel
  refine ⟨sourcePost,targetPost,crepPost,loopPost,sourceRun,targetRun,?_,?_,?_⟩
  · simpa [globalStructCrepProgram] using crepRun
  · simpa [globalStructLoopClock] using loopRun
  · simpa [globalStructLoopClock] using loopBound
end SteppedFlapjack.Concrete
