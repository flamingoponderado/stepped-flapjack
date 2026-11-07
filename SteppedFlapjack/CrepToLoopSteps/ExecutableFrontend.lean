import SteppedFlapjack.LoopLiveSteps.ExecutableBranch
import SteppedFlapjack.CrepToLoopSteps.BitmapSourceShape

/-! A kernel-computable liveness pass for the supported Crep frontend. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps

/-- Before optimization, every supported body has the shape required by the
structural liveness evaluator. -/
theorem supportedCodeBody_rawLoopShape {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) {p : CrepProgHOL width}
    (shape : SupportedCodeBody p) :
    TailEntryShape (compileHOLExact ctxt live p) ∨
      LoopSequenceSource (compileHOLExact ctxt live p) := by
  cases shape with
  | branch h => right; exact .branch (compile_branchProgram_loopBranch h ctxt live)
  | tail h name => left; exact (compiled_tailEntry_shape ctxt live _ h name).1
  | loop hi hc hb ht =>
    right
    exact branchConditionWhileBranch_wordSimpShape _ hi _ hc _ _ hb ht ctxt live
  | @declWhile name value condition body tail hv hc hb ht =>
    right
    have suffix (bc : CrepToLoopContextExact) (bl : NumSet) :
        LoopSequenceSource (compileHOLExact bc bl (.seq (.while condition body) tail)) := by
      obtain ⟨code,conditionValue,next,outLive,condCompiled,loopCompiled,loopBody⟩ :=
        branchConditionWhile_loopBranch condition hc body hb bc bl
      simp only [compileHOLExact,loopCompiled]
      exact .seq (.loop bl bl loopBody) (.branch (compile_branchProgram_loopBranch ht bc bl))
    obtain ⟨value2,compiled⟩ := directExpression_noCode hv ctxt (ctxt.vmax+1) live
    rw [compileHOLExact,compiled]
    exact .seq (.branch .skip) (.seq (.branch (.assign _ _)) (suffix _ _))
  | @declLoop name value init condition body tail hv hi hc hb ht =>
    right
    obtain ⟨value2,compiled⟩ := directExpression_noCode hv ctxt (ctxt.vmax+1) live
    rw [compileHOLExact,compiled]
    exact .seq (.branch .skip) (.seq (.branch (.assign _ _))
      (branchConditionWhileBranch_wordSimpShape init hi condition hc body tail hb ht _ _))

/-- Frontend composition with the structurally executable Loop optimizer. -/
def compileProgWithStructuralLive {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (programs : List (MlString × List Nat × CrepProgHOL width)) :
    List (Nat × List Nat × HolLoopProg width) :=
  let nums := (List.range programs.length).map (fun n => n + firstLoopName)
  let comp := compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable programs)
  List.zipWith (fun n entry => (n,List.range entry.2.1.length,
    optimiseSequence (comp entry.2.1 (crepSimpProgHOL entry.2.2)))) nums programs

/-- On the supported input fragment the executable frontend is exactly the
original compiler, including function numbering and live-set annotations. -/
theorem compileProgWithStructuralLive_eq {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (programs : List (MlString × List Nat × CrepProgHOL width))
    (shapes : ∀ row ∈ programs, SupportedCodeBody row.2.2) :
    compileProgWithStructuralLive arch programs = compileProgHOLExact arch programs := by
  let comp : List Nat → CrepProgHOL width → HolLoopProg width :=
    compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable programs)
  have same : ∀ row ∈ programs,
      optimiseSequence (comp row.2.1 (crepSimpProgHOL row.2.2)) =
        optimiseHOL (comp row.2.1 (crepSimpProgHOL row.2.2)) := by
    intro row member
    have shape := shapes row member
    rw [supportedCodeBody_simp_fixed shape]
    have raw := supportedCodeBody_rawLoopShape
      (mkCtxtExact arch (makeVmapExact row.2.1) (crepToLoopMakeFuncsExactExecutable programs)
        (row.2.1.length - 1)) (listToNumSetHOLExact (List.range row.2.1.length)) shape
    rcases raw with tail | loop
    · exact optimiseSequence_tail_eq tail
    · exact optimiseSequence_eq loop
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

end SteppedFlapjack.CrepToLoopSteps
