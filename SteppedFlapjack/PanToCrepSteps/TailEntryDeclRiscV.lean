import SteppedFlapjack.PanToCrepSteps.TailEntryRiscV
import SteppedFlapjack.CrepToLoopSteps.DeclRiscVComposition
import SteppedFlapjack.PanToCrepSteps.TailEntryDeclBound

/-! Pancake-to-RISC-V composition for a declaration-wrapped loop entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack.Basis.Pure.MlString Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps


open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A Pancake global-entry visit bound supplies the limit for the actual
Crep-to-RISC-V tail-entry simulation under its backend setup conditions. -/
theorem panTailDeclEntry_riscvWithin {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (init : CrepProgHOL 64) (initShape : CrepToLoopSteps.BranchProgram init)
    (localName : Nat) (initializer : CrepExpHOL 64) (initializerShape : CrepToLoopSteps.DirectExpression initializer)
    (calleeInit : CrepProgHOL 64) (calleeInitShape : CrepToLoopSteps.BranchProgram calleeInit)
    (condition : CrepExpHOL 64) (conditionShape : CrepToLoopSteps.DirectExpression condition)
    (body tail : CrepProgHOL 64) (bodyShape : CrepToLoopSteps.BranchProgram body) (tailShape : CrepToLoopSteps.BranchProgram tail)
    (source middle post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (initRun : evalCrepSemHOLProgExact source init = (none,middle))
    (found : middle.code.lookup name = some ([],.dec localName initializer (.seq calleeInit (.seq (.while condition body) tail))))
    (clock : middle.clock ≠ 0)
    (calleeRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []})
      (.dec localName initializer (.seq calleeInit (.seq (.while condition body) tail))) = (result,post))
    (complete : CompleteCrepResult result)
    (crepRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (loopWordRel : loopToWordStateRelHOLExact target word)
    (panLocal : MlS) (panInitializer : ExpHOL 64)
    (panInit panCalleeInit : ProgHOL 64) (panCondition : ExpHOL 64) (panBody panTail : ProgHOL 64)
    (panContext : PanToCrepContextExact 64)
    (panInitializerShape : ScalarExpression panContext panInitializer)
    (panInitShape : PanToCrepSteps.BranchProgram (scalarDeclContext panContext panLocal) panCalleeInit)
    (panConditionShape : ScalarExpression (scalarDeclContext panContext panLocal) panCondition)
    (panBodyShape : PanToCrepSteps.BranchProgram (scalarDeclContext panContext panLocal) panBody)
    (panTailShape : PanToCrepSteps.BranchProgram (scalarDeclContext panContext panLocal) panTail)
    (pan panMiddle panPost : PanSemStateFiniteExact 64 F) (panResult : Option (PanSemResultExact 64))
    (panLocals : HolFiniteMapExact MlString (ValueHOL 64)) (panReturnShape : ShapeHOL)
    (panInitRun : pan.evaluateHOLFiniteState panInit = (none,panMiddle))
    (panLookup : lookupCodeHOLFinite panMiddle.code.lookup name [] =
      some (.dec panLocal .one panInitializer (.seq panCalleeInit (.seq (.while panCondition panBody) panTail)),panLocals,panReturnShape))
    (panClock : panMiddle.clock ≠ 0)
    (panRun : (callEntryStateHOLFinite panMiddle panLocals).evaluateHOLFiniteState
      (.dec panLocal .one panInitializer (.seq panCalleeInit (.seq (.while panCondition panBody) panTail))) = (panResult,panPost))
    (panNonerror : panResult ≠ some .error)
    (panStateRel : panToCrepStateRelFiniteExact (callEntryStateHOLFinite panMiddle panLocals)
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []}))
    (panCodeRel : codeRelExactHOLW panContext (callEntryStateHOLFinite panMiddle panLocals).code
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []}).code)
    (panExcpRel : panToCrepExcpRelFiniteExact panContext.eids (callEntryStateHOLFinite panMiddle panLocals).eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact panContext (callEntryStateHOLFinite panMiddle panLocals).locals
      (decClockCrepSemHOL {middle with locals := HolFiniteMapExact.empty.updateList []}).locals)
    (panLocalised : localisedProgHOL (.dec panLocal .one panInitializer (.seq panCalleeInit (.seq (.while panCondition panBody) panTail))) = true)
    (calleeEq : compileProgExactHOLW panContext (.dec panLocal .one panInitializer (.seq panCalleeInit (.seq (.while panCondition panBody) panTail))) =
      .dec localName initializer (.seq calleeInit (.seq (.while condition body) tail)))
    (panBound : globalEntrySteps panInit name [] pan ≤ limit) :
    let loopEntry := optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))
    let loopLimit := branchTailDeclLoopLimit ctxt live name init localName initializer calleeInit condition body tail
      (sizeOf init + 2 + (4 + sizeOf (compileProgExactHOLW (scalarDeclContext panContext panLocal) panCalleeInit) +
        sizeOf (compileProgExactHOLW (scalarDeclContext panContext panLocal) panBody) + sizeOf (compileProgExactHOLW (scalarDeclContext panContext panLocal) panTail)) * limit)
    panToCrepStateRelFiniteExact panPost post ∧
    pcCompileCorrectResultRel panContext panPost post panResult result ∧
    TailEntryMachineResult post panPost result target word loopEntry loopLimit := by
  have crepFound : middle.code.lookup name = some ([],compileProgExactHOLW panContext
      (.dec panLocal .one panInitializer (.seq panCalleeInit (.seq (.while panCondition panBody) panTail)))) := by
    rw [calleeEq]
    exact found
  have stepBound := tailEntry_decl_crep_bound panInit name panContext panLocal panInitializer panCalleeInit panCondition panBody panTail
    panInitializerShape panInitShape panConditionShape panBodyShape panTailShape pan panMiddle panPost panResult panLocals panReturnShape
    source middle init initShape panInitRun panLookup panClock panRun panNonerror initRun crepFound clock
    panStateRel panCodeRel panExcpRel panLocalsRel panLocalised
  have bound : CrepSteps.steps (.seq init (.call none name [])) source ≤
      sizeOf init + 2 + (4 + sizeOf (compileProgExactHOLW (scalarDeclContext panContext panLocal) panCalleeInit) +
        sizeOf (compileProgExactHOLW (scalarDeclContext panContext panLocal) panBody) + sizeOf (compileProgExactHOLW (scalarDeclContext panContext panLocal) panTail)) * limit := by
    exact stepBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ panBound) _)
  obtain ⟨postRel,resultRel⟩ := tailEntry_source_result _ _ _ _ _ _ _ _ _
    panRun panNonerror panStateRel panCodeRel panExcpRel panLocalsRel panLocalised calleeEq calleeRun
  refine ⟨postRel,resultRel,?_⟩
  have machine := branchTailDecl_riscvWithin ctxt live name init initShape localName initializer initializerShape calleeInit calleeInitShape condition conditionShape
    body tail bodyShape tailShape source middle post result target word _ initRun found clock calleeRun complete
    crepRel memRel globalsRel codeRel localsRel loopWordRel bound
  have ffi : panPost.ffi = post.ffi := postRel.2.2.2.2.2.2.2.1
  simpa only [TailEntryMachineResult,ffi] using machine

end SteppedFlapjack.PanToCrepSteps
