import SteppedFlapjack.CrepToLoopSteps.DeclTerminal
import SteppedFlapjack.LoopToWordSteps.TailEntryRiscV

/-! Machine-backend inputs for an entry calling a declaration-wrapped loop. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- Loop replay limit derived from the Crep entry's visit bound. -/
noncomputable def branchTailDeclLoopLimit (ctxt : CrepToLoopContextExact) (live : NumSet) (callee : MlString)
    (entryInit : CrepProgHOL 64) (name : Nat) (e : CrepExpHOL 64) (init : CrepProgHOL 64)
    (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64) (limit : Nat) : Nat :=
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p : CrepProgHOL 64 := .dec name e (.seq init (.seq (.while condition body) tail))
  let bc := {c with vars := c.vars.updateEq (name,c.vmax+1), vmax := c.vmax+1}
  let bl := sptInsert (c.vmax+1) () .ln
  let factor := 1 + sizeOf (compileHOLExact bc bl init) +
    (1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
      (sizeOf (compileHOLExact bc bl body)+3) + sizeOf (compileHOLExact bc bl tail))
  let entry := optimiseHOL (compileHOLExact ctxt live (.seq entryInit (.call none callee [])))
  let compiledCallee := ocompileHOLExact c .ln p
  (sizeOf entry + sizeOf compiledCallee) *
    (2 * (4 + sizeOf (compileHOLExact ctxt live entryInit) +
      sizeOf compiledCallee * (2 * ((factor+4) * (limit+1)) + 1)) + 1)

/-- The actual optimized Loop entry and callee provide all Loop-side semantic
and shape inputs to the RISC-V tail-entry theorem. -/
theorem branchTailDecl_riscv_inputs {F C : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (callee : MlString)
    (entryInit : CrepProgHOL 64) (entryShape : BranchProgram entryInit)
    (name : Nat) (e : CrepExpHOL 64) (shape : DirectExpression e)
    (init : CrepProgHOL 64) (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (initShape : BranchProgram init) (conditionShape : DirectExpression condition)
    (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 C F) (limit : Nat)
    (initRun : evalCrepSemHOLProgExact source entryInit = (none,middle))
    (found : middle.code.lookup callee = some ([],.dec name e (.seq init (.seq (.while condition body) tail))))
    (clock : middle.clock ≠ 0)
    (calleeRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []})
      (.dec name e (.seq init (.seq (.while condition body) tail))) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (loopWordRel : loopToWordStateRelHOLExact target word)
    (sourceBound : CrepSteps.steps (.seq entryInit (.call none callee [])) source ≤ limit) :
    let entry := optimiseHOL (compileHOLExact ctxt live (.seq entryInit (.call none callee [])))
    let compiledCallee := ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
      (.dec name e (.seq init (.seq (.while condition body) tail)))
    ∃ extra loopPost,
      LoopLiveSteps.SingleTailEntryShape (findLabExact ctxt callee) entry ∧
      LoopSequenceSource compiledCallee ∧
      sptLookup (findLabExact ctxt callee) {target with clock := target.clock+extra}.code = some ([],compiledCallee) ∧
      evaluate entry {target with clock := target.clock+extra} = (resultToLoop result,loopPost) ∧
      resultToLoop result ≠ some .error ∧ CompleteLoopResult (resultToLoop result) ∧
      loopToWordStateRelHOLExact {target with clock := target.clock+extra} {word with clock := word.clock+extra} ∧
      crepToLoopStateRelExact post loopPost ∧
      LoopSteps.steps entry {target with clock := target.clock+extra} ≤
        branchTailDeclLoopLimit ctxt live callee entryInit name e init condition body tail limit := by
  obtain ⟨extra,loopPost,run,_,postRel,bound⟩ :=
    branch_tailCall_nil_decl_optimised_bound ctxt live callee entryInit entryShape name e shape init condition body tail
      initShape conditionShape bodyShape tailShape source middle post result target .ln (0,0)
      initRun found clock calleeRun complete stateRel memRel globalsRel codeRel localsRel
  have foundSource : source.code.lookup callee = some ([],.dec name e (.seq init (.seq (.while condition body) tail))) := by
    simpa only [evaluateCodeInvariantHOL entryInit source none middle initRun] using found
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 callee [] _ foundSource
  have lenZero : len = 0 := by simpa using hlen.symm
  subst len
  have label : findLabExact ctxt callee = loc := by simp [findLabExact,hlab]
  have lookup : sptLookup (findLabExact ctxt callee) {target with clock := target.clock+extra}.code =
      some ([],ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
        (.dec name e (.seq init (.seq (.while condition body) tail)))) := by
    simpa [label,listToNumSetHOLExact] using hcode
  have shifted : loopToWordStateRelHOLExact {target with clock := target.clock+extra}
      {word with clock := word.clock+extra} := by
    rcases loopWordRel with ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    refine ⟨len,hm,hd,hs,?_,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    simp only
    omega
  have bounded : LoopSteps.steps (optimiseHOL (compileHOLExact ctxt live (.seq entryInit (.call none callee []))))
      {target with clock := target.clock+extra} ≤
      branchTailDeclLoopLimit ctxt live callee entryInit name e init condition body tail limit := by
    refine bound.trans ?_
    dsimp [branchTailDeclLoopLimit]
    gcongr
  have calleeShape : LoopSequenceSource (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln
      (.dec name e (.seq init (.seq (.while condition body) tail)))) := by
    simpa only [ocompileHOLExact] using LoopLiveSteps.optimise_sequence
      (directDecl_branchWhileBranch_shape name e shape init condition body tail initShape conditionShape
        bodyShape tailShape (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln)
  exact ⟨extra,loopPost,LoopLiveSteps.optimise_singleTail
    (LoopLiveSteps.compiled_singleTail_shape ctxt live entryInit entryShape callee),calleeShape,
    lookup,run,by cases complete <;> simp [resultToLoop],completeCrep_loop complete,shifted,postRel,bounded⟩

end SteppedFlapjack.CrepToLoopSteps
