import SteppedFlapjack.PanToCrepSteps.WhileSteps
import SteppedFlapjack.CrepToLoopSteps.ExecutableFrontend
import SteppedFlapjack.CrepToLoopSteps.ScalarProgram
import SteppedFlapjack.LoopLiveSteps.TailEntryGlobalBound
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopLiveSteps

private theorem frontend_arguments_scalar {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (args : List (ExpHOL width))
    (shape : ∀ e ∈ args, FrontendScalar ctxt e) :
    ∀ e ∈ (compileExpExactHOLWList ctxt args).flatMap Prod.fst, CompiledScalar e := by
  induction args with
  | nil => simp [compileExpExactHOLWList]
  | cons e es ih =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled (shape e (by simp))
    have tail := ih (by intro x hx; exact shape x (by simp [hx]))
    simp only [compileExpExactHOLWList,compiled,List.flatMap_cons,List.mem_append,List.mem_singleton] at ⊢
    intro x hx
    rcases hx with rfl | hx
    · exact scalar
    · exact tail x hx

private theorem nested_zero_decl_shape {width : Nat} [NeZero width]
    (names : List Nat) (body : CrepProgHOL width)
    (bodyShape : ∀ ctxt live, SimpleLoopSequenceSource (compileHOLExact ctxt live body)) :
    ∀ ctxt live, SimpleLoopSequenceSource (compileHOLExact ctxt live
      (nestedDecsHOL names (List.replicate names.length (.const (0 : BitVec width))) body)) := by
  induction names with
  | nil => simpa [nestedDecsHOL] using bodyShape
  | cons name names ih =>
    intro ctxt live
    simp only [List.length_cons,List.replicate_succ,nestedDecsHOL]
    exact compiled_decl_scalar_shape ctxt live name _ _ (.direct (.const _)) ih

/-- Actual Pancake frontend programs with calls compile to the recursive Loop
optimizer shape, for every Crep-to-Loop context. -/
theorem callFrontend_compiled_loopShape {width : Nat} [NeZero width]
    {ctxt : PanToCrepContextExact width} {p : ProgHOL width} (shape : CallFrontend ctxt p) :
    ∀ lc live, SimpleLoopSequenceSource (compileHOLExact lc live (compileProgExactHOLW ctxt p)) := by
  induction shape with
  | base h =>
    intro lc live
    exact compiled_scalarProgram_shape (frontend_scalar_program h) lc live
  | @tail ctxt fname args ha =>
    intro lc live
    simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW]
    apply compiled_tailCall_scalar_shape
    exact frontend_arguments_scalar ctxt args ha
  | @decCall ctxt name shape fname args cont ha hb ih =>
    intro lc live
    simp only [compileProgExactHOLW,compileDecCallExactHOLW]
    apply nested_zero_decl_shape
    intro lc live
    rw [compileHOLExact]
    exact .seq (compiled_returningCall_scalar_shape lc live fname _ (frontend_arguments_scalar ctxt args ha) _)
      (ih lc live)
  | @decl ctxt name e body he hb ih =>
    intro lc live
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL]
    exact compiled_decl_scalar_shape lc live _ value _ scalar ih
  | @seq ctxt a b ha hb iha ihb =>
    intro lc live
    simpa only [compileProgExactHOLW,compileHOLExact] using
      (SimpleLoopSequenceSource.seq (iha lc live) (ihb lc live))
  | @ite ctxt e a b he ha hb iha ihb =>
    intro lc live
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp only [compileProgExactHOLW,compileIfExactHOLW,compiled]
    exact compiled_conditional_scalar_shape lc live value _ _ scalar (iha lc live) (ihb lc live)
  | @«while» ctxt e body he hb ih =>
    intro lc live
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp only [compileProgExactHOLW,compileWhileExactHOLW,compiled]
    exact compiled_while_scalar_shape lc live value _ scalar (ih lc live)
/-- Optimizing the compiled source preserves the call-aware recursive shape. -/
theorem callFrontend_optimised_loopShape {width : Nat} [NeZero width]
    {ctxt : PanToCrepContextExact width} {p : ProgHOL width} (shape : CallFrontend ctxt p)
    (lc : CrepToLoopContextExact) (live : NumSet) :
    SimpleLoopSequenceSource (optimiseHOL (compileHOLExact lc live (compileProgExactHOLW ctxt p))) :=
  optimise_simpleSequence (callFrontend_compiled_loopShape shape lc live)

private theorem scalar_arguments_simp_fixed {width : Nat} [NeZero width]
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e) :
    args.map crepSimpExpHOL = args := by
  induction args with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons]
    rw [branchCondition_simp_fixed (shape e (by simp)), ih (by intro x hx; exact shape x (by simp [hx]))]

private theorem nested_zero_decl_simp_fixed {width : Nat} [NeZero width]
    (names : List Nat) (body : CrepProgHOL width) (fixed : crepSimpProgHOL body = body) :
    crepSimpProgHOL (nestedDecsHOL names (List.replicate names.length (.const (0 : BitVec width))) body) =
      nestedDecsHOL names (List.replicate names.length (.const (0 : BitVec width))) body := by
  induction names with
  | nil => simpa [nestedDecsHOL] using fixed
  | cons name names ih =>
    simp only [List.length_cons,List.replicate_succ,nestedDecsHOL,crepSimpProgHOL,crepSimpExpHOL,ih]

/-- The actual Crep simplifier leaves call-aware frontend output unchanged. -/
theorem callFrontend_simp_fixed {width : Nat} [NeZero width]
    {ctxt : PanToCrepContextExact width} {p : ProgHOL width} (shape : CallFrontend ctxt p) :
    crepSimpProgHOL (compileProgExactHOLW ctxt p) = compileProgExactHOLW ctxt p := by
  induction shape with
  | base h => exact scalarProgram_simp_fixed (frontend_scalar_program h)
  | @tail ctxt fname args ha =>
    have fixed := scalar_arguments_simp_fixed _ (frontend_arguments_scalar ctxt args ha)
    simpa [compileProgExactHOLW,compileCallNoReturnExactHOLW,crepSimpProgHOL] using fixed
  | @decCall ctxt name shape fname args cont ha hb ih =>
    have fixed := scalar_arguments_simp_fixed _ (frontend_arguments_scalar ctxt args ha)
    simp only [compileProgExactHOLW,compileDecCallExactHOLW]
    apply nested_zero_decl_simp_fixed
    simp only [crepSimpProgHOL,fixed,ih]
  | @decl ctxt name e body he hb ih =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,crepSimpProgHOL,
      branchCondition_simp_fixed scalar]
    simpa [scalarDeclContext] using ih
  | seq ha hb iha ihb => simp [compileProgExactHOLW,crepSimpProgHOL,iha,ihb]
  | @ite ctxt e a b he ha hb iha ihb =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileIfExactHOLW,compiled,crepSimpProgHOL,
      branchCondition_simp_fixed scalar,iha,ihb]
  | @«while» ctxt e body he hb ih =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileWhileExactHOLW,compiled,crepSimpProgHOL,
      branchCondition_simp_fixed scalar,ih]

/-- For a table of actual call-aware frontend bodies, the executable
structural optimizer computes exactly the original whole Crep-to-Loop compiler. -/
theorem callFrontend_compileProgWithStructuralLive_eq {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctxt : PanToCrepContextExact width) (p : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctxt p ∧ CallFrontend ctxt p) :
    compileProgWithStructuralLive arch programs = compileProgHOLExact arch programs := by
  apply compileProgWithStructuralLive_eq_of_shapes arch programs
  · intro row member
    obtain ⟨ctxt,p,eq,shape⟩ := sources row member
    rw [eq]
    exact callFrontend_simp_fixed shape
  · intro row member
    obtain ⟨ctxt,p,eq,shape⟩ := sources row member
    rw [eq]
    unfold compFuncHOLExact
    exact callFrontend_compiled_loopShape shape _ _

/-- Every body produced by the actual compiler has the call-aware Loop shape. -/
theorem callFrontend_compileProg_loopShapes {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctxt : PanToCrepContextExact width) (p : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctxt p ∧ CallFrontend ctxt p) :
    ∀ name params body, (name,params,body) ∈ compileProgHOLExact arch programs →
      SimpleLoopSequenceSource body := by
  let comp := compFuncHOLExact (width := width) arch (crepToLoopMakeFuncsExactExecutable programs)
  have zipShape : ∀ (ns : List Nat) (entries : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)),
      (∀ row ∈ entries, row ∈ programs) →
      ∀ output ∈ List.zipWith (fun n entry => (n,List.range entry.2.1.length,
        optimiseHOL (comp entry.2.1 (crepSimpProgHOL entry.2.2)))) ns entries,
        SimpleLoopSequenceSource output.2.2 := by
    intro ns
    induction ns with
    | nil => intro entries subset output member; simp at member
    | cons n ns ih =>
      intro entries subset output member
      cases entries with
      | nil => simp at member
      | cons entry entries =>
        simp only [List.zipWith,List.mem_cons] at member
        rcases member with rfl | member
        · obtain ⟨ctxt,p,eq,shape⟩ := sources entry (subset entry (by simp))
          rw [eq,callFrontend_simp_fixed shape]
          unfold comp compFuncHOLExact
          exact callFrontend_optimised_loopShape shape _ _
        · exact ih entries (by intro row member; exact subset row (by simp [member])) output member
  intro name params body member
  exact zipShape _ programs (by intros; assumption) (name,params,body) member

/-- Actual compiled function tables discharge the global Loop bound's shape
premise using only their call-aware source bodies. -/
theorem callFrontend_compiled_loopTableSupported {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctxt : PanToCrepContextExact width) (p : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctxt p ∧ CallFrontend ctxt p) :
    LoopTableSupported (sptFromAList (compileProgHOLExact arch programs)) := by
  intro name params body lookup
  rw [sptLookup_sptFromAList] at lookup
  exact callFrontend_compileProg_loopShapes arch programs sources name params body
    (sptAListLookup_mem name _ (params,body) lookup)

end SteppedFlapjack.CrepToLoopSteps
