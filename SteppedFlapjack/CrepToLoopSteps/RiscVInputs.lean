import SteppedFlapjack.CrepToLoopSteps.TailRiscVInputsCommon
import SteppedFlapjack.CrepToLoopSteps.OptimisedTailEntry
import SteppedFlapjack.LoopToWordSteps.TailEntryRiscV

/-! Derive the Loop inputs to the RISC-V simulation from a Crep execution. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- The source-dependent Loop replay limit for a branch initializer followed
by a zero-argument call to an initialized while loop. -/
noncomputable def branchTailLoopLimit (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (init calleeInit : CrepProgHOL 64) (condition : CrepExpHOL 64)
    (body tail : CrepProgHOL 64) (limit : Nat) : Nat :=
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p : CrepProgHOL 64 := .seq calleeInit (.seq (.while condition body) tail)
  let entry := optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))
  let callee := ocompileHOLExact c .ln p
  let factor := 1 + sizeOf (compileHOLExact c .ln calleeInit) +
    (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
      (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
        sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))
  (sizeOf entry + sizeOf callee) *
    (2 * (4 + sizeOf (compileHOLExact ctxt live init) +
      sizeOf callee * (2 * (factor * (limit+1)) + 1)) + 1)

/-- All Loop-side semantic and shape inputs to the tail-entry RISC-V theorem,
including its source-visit limit, follow from the completed Crep execution.
The same extra clock is added to both Loop and Word states. -/
theorem branchTail_riscv_inputs {F C : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (calleeInit : CrepProgHOL 64) (calleeInitShape : BranchProgram calleeInit)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 C F) (limit : Nat)
    (initRun : evalCrepSemHOLProgExact source init = (none,middle))
    (found : middle.code.lookup name = some ([],.seq calleeInit (.seq (.while condition body) tail)))
    (clock : middle.clock ≠ 0)
    (calleeRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []})
      (.seq calleeInit (.seq (.while condition body) tail)) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (loopWordRel : loopToWordStateRelHOLExact target word)
    (sourceBound : CrepSteps.steps (.seq init (.call none name [])) source ≤ limit) :
    let entry := optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))
    let callee := ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
      (.seq calleeInit (.seq (.while condition body) tail))
    ∃ extra loopPost,
      LoopLiveSteps.SingleTailEntryShape (findLabExact ctxt name) entry ∧
      LoopSequenceSource callee ∧
      sptLookup (findLabExact ctxt name) {target with clock := target.clock+extra}.code = some ([],callee) ∧
      evaluate entry {target with clock := target.clock+extra} = (resultToLoop result,loopPost) ∧
      resultToLoop result ≠ some .error ∧ CompleteLoopResult (resultToLoop result) ∧
      loopToWordStateRelHOLExact {target with clock := target.clock+extra} {word with clock := word.clock+extra} ∧
      crepToLoopStateRelExact post loopPost ∧
      LoopSteps.steps entry {target with clock := target.clock+extra} ≤
        branchTailLoopLimit ctxt live name init calleeInit condition body tail limit := by
  obtain ⟨extra,loopPost,run,_,postRel,bound⟩ :=
    branch_tailCall_nil_optimised_bound ctxt live name init initShape calleeInit calleeInitShape
      condition conditionShape body tail bodyShape tailShape source middle post result target .ln (0,0)
      initRun found clock calleeRun complete stateRel memRel globalsRel codeRel localsRel
  have bounded : LoopSteps.steps (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name []))))
      {target with clock := target.clock+extra} ≤
      branchTailLoopLimit ctxt live name init calleeInit condition body tail limit := by
    refine bound.trans ?_
    dsimp [branchTailLoopLimit]
    gcongr
  have calleeShape : LoopSequenceSource (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
      (.seq calleeInit (.seq (.while condition body) tail))) := by
    simpa only [ocompileHOLExact] using LoopLiveSteps.optimise_sequence
      (branchConditionWhileBranch_wordSimpShape calleeInit calleeInitShape condition conditionShape
        body tail bodyShape tailShape (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln)
  exact ⟨extra,loopPost,branchTail_riscv_inputs_of_run ctxt live name init
    (.seq calleeInit (.seq (.while condition body) tail)) initShape source middle post result target word extra loopPost _
    initRun found complete codeRel loopWordRel calleeShape run postRel bounded⟩

end SteppedFlapjack.CrepToLoopSteps
