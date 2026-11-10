import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.CrepToLoopSteps.TailCallSteps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopIteration
import Flapjack.Misc.BalancedMap.Core
import SteppedFlapjack.LoopLiveSteps.ExecutableBranch

/-! A kernel-computable liveness pass for the supported Crep frontend. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps

private theorem assignmentSequence_shape {width : Nat} [NeZero width]
    (regs : List Nat) (values : List (HolLoopExp width)) (call : HolLoopProg width)
    (shape : SimpleLoopSequenceSource call) :
    SimpleLoopSequenceSource (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign values ++ [call])) := by
  induction regs generalizing values with
  | nil => simp [loopNestedSeqHOL]; exact .seq shape (.branch .skip)
  | cons reg regs ih =>
    cases values with
    | nil => simp [loopNestedSeqHOL]; exact .seq shape (.branch .skip)
    | cons value values =>
      simp only [List.zipWith_cons_cons,List.cons_append,loopNestedSeqHOL]
      exact .seq (.branch (.assign reg value)) (ih values)

/-- Direct-argument tail calls have the supported structural optimizer shape. -/
theorem compiled_tailCall_direct_shape {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e) :
    SimpleLoopSequenceSource (compileHOLExact ctxt live (.call none name args)) := by
  obtain ⟨values,_,compiled⟩ := compile_tailCall_direct ctxt live name args shape
  rw [compiled]
  exact assignmentSequence_shape _ _ _ (.tail _ _)

/-- Direct-argument returning calls have the supported structural optimizer shape. -/
theorem compiled_returningCall_direct_shape {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames) :
    SimpleLoopSequenceSource (compileHOLExact ctxt live (.call (some (names,none)) name args)) := by
  obtain ⟨values,_,compiled⟩ := compile_returningCall_direct ctxt live name args shape names returnNames mapped
  rw [compiled]
  exact assignmentSequence_shape _ _ _ (.returning _ _ _ _ _ _)

/-- Before optimization, every supported body has the shape required by the
structural liveness evaluator. -/
theorem supportedCodeBody_rawLoopShape {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) {p : CrepProgHOL width}
    (shape : SupportedCodeBody p) :
    TailEntryShape (compileHOLExact ctxt live p) ∨
      SimpleLoopSequenceSource (compileHOLExact ctxt live p) := by
  cases shape with
  | branch h => right; exact .branch (compile_branchProgram_loopBranch h ctxt live)
  | tail h name => left; exact (compiled_tailEntry_shape ctxt live _ h name).1
  | loop hi hc hb ht =>
    right
    obtain ⟨code,value,next,outLive,compiled,loopCompiled,loopBody⟩ :=
      branchConditionWhile_loopBranch _ (BranchCondition.toScalar hc) _ hb ctxt live
    simp only [compileHOLExact,loopCompiled]
    exact .seq (.branch (compile_branchProgram_loopBranch hi ctxt live))
      (.seq (.loop live live loopBody) (.branch (compile_branchProgram_loopBranch ht ctxt live)))
  | @declWhile name value condition body tail hv hc hb ht =>
    right
    have suffix (bc : CrepToLoopContextExact) (bl : NumSet) :
        SimpleLoopSequenceSource (compileHOLExact bc bl (.seq (.while condition body) tail)) := by
      obtain ⟨code,conditionValue,next,outLive,condCompiled,loopCompiled,loopBody⟩ :=
        branchConditionWhile_loopBranch condition (BranchCondition.toScalar hc) body hb bc bl
      simp only [compileHOLExact,loopCompiled]
      exact .seq (.loop bl bl loopBody) (.branch (compile_branchProgram_loopBranch ht bc bl))
    obtain ⟨value2,compiled⟩ := directExpression_noCode hv ctxt (ctxt.vmax+1) live
    rw [compileHOLExact,compiled]
    exact .seq (.branch .skip) (.seq (.branch (.assign _ _)) (suffix _ _))
  | @declLoop name value init condition body tail hv hi hc hb ht =>
    right
    have suffix (bc : CrepToLoopContextExact) (bl : NumSet) :
        SimpleLoopSequenceSource (compileHOLExact bc bl (.seq init (.seq (.while condition body) tail))) := by
      obtain ⟨code,conditionValue,next,outLive,condCompiled,loopCompiled,loopBody⟩ :=
        branchConditionWhile_loopBranch condition (BranchCondition.toScalar hc) body hb bc bl
      simp only [compileHOLExact,loopCompiled]
      exact .seq (.branch (compile_branchProgram_loopBranch hi bc bl))
        (.seq (.loop bl bl loopBody) (.branch (compile_branchProgram_loopBranch ht bc bl)))
    obtain ⟨value2,compiled⟩ := directExpression_noCode hv ctxt (ctxt.vmax+1) live
    rw [compileHOLExact,compiled]
    exact .seq (.branch .skip) (.seq (.branch (.assign _ _)) (suffix _ _))

/-- Frontend composition with the structurally executable Loop optimizer. -/
def compileProgWithStructuralLive {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (programs : List (MlString × List Nat × CrepProgHOL width)) :
    List (Nat × List Nat × HolLoopProg width) :=
  let nums := (List.range programs.length).map (fun n => n + firstLoopName)
  let comp := compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable programs)
  List.zipWith (fun n entry => (n,List.range entry.2.1.length,
    optimiseSequence (comp entry.2.1 (crepSimpProgHOL entry.2.2)))) nums programs

/-- The executable frontend agrees with the original compiler whenever the
actual function bodies and their compiled Loop forms satisfy the checked shapes. -/
theorem compileProgWithStructuralLive_eq_of_shapes {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (programs : List (MlString × List Nat × CrepProgHOL width))
    (fixed : ∀ row ∈ programs, crepSimpProgHOL row.2.2 = row.2.2)
    (shapes : ∀ row ∈ programs, SimpleLoopSequenceSource
      (compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable programs) row.2.1 row.2.2)) :
    compileProgWithStructuralLive arch programs = compileProgHOLExact arch programs := by
  let comp : List Nat → CrepProgHOL width → HolLoopProg width :=
    compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable programs)
  have same : ∀ row ∈ programs,
      optimiseSequence (comp row.2.1 (crepSimpProgHOL row.2.2)) =
        optimiseHOL (comp row.2.1 (crepSimpProgHOL row.2.2)) := by
    intro row member
    rw [fixed row member]
    exact optimiseSequence_eq (shapes row member)
  have zipEq : ∀ (nums : List Nat) (rows : List (MlString × List Nat × CrepProgHOL width)),
      (∀ row ∈ rows, row ∈ programs) →
      List.zipWith (fun n row => (n,List.range row.2.1.length,
        optimiseSequence (comp row.2.1 (crepSimpProgHOL row.2.2)))) nums rows =
      List.zipWith (fun n row => (n,List.range row.2.1.length,
        optimiseHOL (comp row.2.1 (crepSimpProgHOL row.2.2)))) nums rows := by
    intro nums
    induction nums with
    | nil => intro rows subset; simp
    | cons n ns ih =>
      intro rows subset
      cases rows with
      | nil => rfl
      | cons row rest =>
        simp only [List.zipWith_cons_cons]
        rw [same row (subset row (by simp)), ih rest (by
          intro item member
          exact subset item (by simp [member]))]
  exact zipEq _ _ (by intros; assumption)

/-- Existing supported bodies instantiate the shared structural compiler proof. -/
theorem compileProgWithStructuralLive_eq {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (programs : List (MlString × List Nat × CrepProgHOL width))
    (shapes : ∀ row ∈ programs, SupportedCodeBody row.2.2) :
    compileProgWithStructuralLive arch programs = compileProgHOLExact arch programs := by
  apply compileProgWithStructuralLive_eq_of_shapes arch programs
  · intro row member
    exact supportedCodeBody_simp_fixed (shapes row member)
  · intro row member
    have raw := supportedCodeBody_rawLoopShape
      (mkCtxtExact arch (makeVmapExact row.2.1) (crepToLoopMakeFuncsExactExecutable programs)
        (row.2.1.length - 1)) (listToNumSetHOLExact (List.range row.2.1.length)) (shapes row member)
    rcases raw with tail | loop
    · exact tailEntry_to_simple tail
    · exact loop

end SteppedFlapjack.CrepToLoopSteps
