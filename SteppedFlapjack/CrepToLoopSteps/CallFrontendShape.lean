import SteppedFlapjack.PanToCrepSteps.WhileSteps
import SteppedFlapjack.PanToCrepSteps.ConcreteDeclInitial
import SteppedFlapjack.CrepToLoopSteps.ExecutableFrontend
import SteppedFlapjack.CrepToLoopSteps.ScalarProgram
import SteppedFlapjack.CrepSteps.CallClock
import SteppedFlapjack.CrepToLoopSteps.CallCost
import SteppedFlapjack.CrepToLoopSteps.TailCallSteps
import SteppedFlapjack.LoopLiveSteps.TailEntryGlobalBound
import Flapjack.Pancake.CrepInline.InlineRouteBridge
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
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

/-- Every function emitted by declaration compilation originates from a
call-aware source body in the exact context used by the compiler. -/
theorem callFrontend_declaration_sources {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1) :
    ∀ row ∈ compileToCrepExactHOLW declarations,
      ∃ (ctxt : PanToCrepContextExact width) (p : ProgHOL width),
        row.2.2 = compileProgExactHOLW ctxt p ∧ CallFrontend ctxt p := by
  intro row member
  simp only [compileToCrepExactHOLW,List.mem_map] at member
  obtain ⟨entry,mem,rfl⟩ := member
  exact ⟨_,_,rfl,shapes entry mem⟩

/-- Every lookup in a call-aware declaration table has the callee context
used by the source-to-Crep clock induction. -/
theorem callFrontend_declaration_table {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1) :
    CallFrontendCode
      (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
        (getEidsFromDeclsHOL declarations))
      (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse) := by
  intro name params body rsh found
  change Flapjack.FLOOKUP (Flapjack.FUPDATE_LIST Flapjack.FEMPTY
    (functionsHOL declarations).reverse) name = some (params,body,rsh) at found
  rw [Flapjack.FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at found
  have member : (name,params,body,rsh) ∈ functionsHOL declarations := by
    obtain ⟨before,after,split,_⟩ := List.lookup_eq_some_iff.mp found
    rw [split]
    simp
  have shape := shapes (name,params,body,rsh) member
  have contextEq : mkCtxtExactHOL (panToCrepMakeVmapHOLExact params)
      (makeFuncsExactHOL (functionsHOL declarations))
      (sizeOfShapeHOL (.comb (params.map Prod.snd)) - 1) (getEidsFromDeclsHOL declarations) =
      ctxtFcExactHOL (makeFuncsExactHOL (functionsHOL declarations)) (getEidsFromDeclsHOL declarations)
        (params.map Prod.fst) (params.map Prod.snd) (List.range (sizeOfShapeHOL (.comb (params.map Prod.snd)))) := by
    simp [mkCtxtExactHOL,ctxtFcExactHOL,panToCrepMakeVmapHOLExact,maxList_range,List.zip]
  rw [contextEq] at shape
  exact shape

/-- A call-aware declaration table supplies the original Pancake-to-Crep code
relation for the actual compiler output when inlining is disabled. -/
theorem callFrontend_declaration_codeRel {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (unique : ((functionsHOL declarations).map Prod.fst).Nodup)
    (noInline : (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1) :
    codeRelExactHOLW
      (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
        (getEidsFromDeclsHOL declarations))
      (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)
      (HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW declarations).reverse) := by
  have localised : ∀ entry ∈ functionsHOL declarations, localisedProgHOL entry.2.2.1 = true := by
    intro entry member
    exact callFrontend_localised (shapes entry member)
  have relation := mkCtxtCodeImpCodeRelExactHOLW declarations unique localised
  rw [compileProgDeclsHOLW, noInline, CrepInlineRoute.compileInlTopHOLExact_nil]
  exact relation

/-- The source visit bound transfers to the actual Crep table for any
call-aware declaration list in a concrete empty-local source configuration. -/
theorem callFrontend_declaration_steps {σ : Type}
    (declarations : List (DeclHOL 64))
    (unique : ((functionsHOL declarations).map Prod.fst).Nodup)
    (noInline : (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1)
    (program : ProgHOL 64)
    (shape : CallFrontend (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)) program)
    (source sourceFinal : Flapjack.PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (code : source.code = HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (noExceptions : getEidsFromDeclsHOL declarations = HolFiniteMapExact.empty)
    (run : source.evaluateHOLFiniteState program = (result,sourceFinal)) (nonerror : result ≠ some .error) :
    let ctxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
      (getEidsFromDeclsHOL declarations)
    let programs := compileProgDeclsHOLW declarations
    ∃ targetResult targetFinal,
      evalCrepSemHOLProgExact (concreteDeclCrepState source programs) (compileProgExactHOLW ctxt program) =
        (targetResult,targetFinal) ∧
      panToCrepStateRelFiniteExact sourceFinal targetFinal ∧
      codeRelExactHOLW ctxt sourceFinal.code targetFinal.code ∧
      panToCrepExcpRelFiniteExact ctxt.eids sourceFinal.eshapes ∧
      pcCompileCorrectResultRel ctxt sourceFinal targetFinal result targetResult ∧
      CrepSteps.steps (compileProgExactHOLW ctxt program) (concreteDeclCrepState source programs) ≤
        max (CrepSteps.statementWeight (compileProgExactHOLW ctxt program)) (CrepSteps.codeWeight programs) *
          controlSteps program source := by
  let ctxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
    (getEidsFromDeclsHOL declarations)
  let programs := compileProgDeclsHOLW declarations
  have table : CallFrontendCode ctxt source.code := by
    rw [code]
    exact callFrontend_declaration_table declarations shapes
  have related : codeRelExactHOLW ctxt source.code (concreteDeclCrepState source programs).code := by
    rw [code]
    exact callFrontend_declaration_codeRel declarations unique noInline shapes
  have stateRel := concreteDecl_panCrep_stateRel source programs structs globals
  have excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes := by
    simpa [ctxt,mkCtxtExactHOL,noExceptions,exceptions] using (empty_panCrep_exceptions (width := 64))
  have localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals (concreteDeclCrepState source programs).locals := by
    rw [locals]
    apply empty_panCrep_locals
    rfl
  have bound := callFrontend_compiled_steps ctxt program shape source sourceFinal result (concreteDeclCrepState source programs)
    programs rfl table run nonerror stateRel related excpRel localsRel
  have correct : pcCompileCorrectAt program source := (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨targetResult,targetFinal,targetRun,finalState,finalCode,finalExcp,resultRel⟩ :=
    correct result sourceFinal (concreteDeclCrepState source programs) ctxt run nonerror stateRel related excpRel localsRel
      (callFrontend_localised shape)
  exact ⟨targetResult,targetFinal,targetRun,finalState,finalCode,finalExcp,resultRel,bound⟩

/-- The actual post-inline compiler table has the call-aware Loop shape when
no declarations request inlining. The condition is decidable from the source. -/
theorem callFrontend_declaration_loopTableSupported {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (declarations : List (DeclHOL width))
    (noInline : (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1) :
    LoopTableSupported (sptFromAList (compileProgHOLExact arch (compileProgDeclsHOLW declarations))) := by
  rw [compileProgDeclsHOLW,noInline,CrepInlineRoute.compileInlTopHOLExact_nil]
  exact callFrontend_compiled_loopTableSupported arch _ (callFrontend_declaration_sources declarations shapes)

/-- The actual compiled call-aware declaration table has the original
Crep-to-Loop code relation, without a separate simplifier fixed-point premise. -/
theorem callFrontend_declaration_crepLoop_codeRel {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (declarations : List (DeclHOL width))
    (noInline : (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ functionsHOL declarations,
      CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (functionsHOL declarations))
        (sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1)
    (start : Flapjack.Basis.Pure.MlString.MlString) (entry : CrepProgHOL width)
    (unique : ((functionsHOL declarations).map Prod.fst).Nodup)
    (found : holAlookup (compileProgDeclsHOLW declarations) start = some ([],entry)) :
    let programs := compileProgDeclsHOLW declarations
    crepToLoopCodeRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0)
      (alistToFmapCodeExact programs) (sptFromAList (compileProgHOLExact arch programs)) := by
  have compiledUnique : ((compileProgDeclsHOLW declarations).map Prod.fst).Nodup := by
    rw [compileProgDeclsHOLW,noInline,CrepInlineRoute.compileInlTopHOLExact_nil]
    simpa [compileToCrepExactHOLW,List.map_map,Function.comp_def] using unique
  apply wholeCrep_fixed_executable_codeRel _ _ start entry compiledUnique found
  intro name params body member
  rw [compileProgDeclsHOLW,noInline,CrepInlineRoute.compileInlTopHOLExact_nil] at member
  obtain ⟨ctxt,p,eq,shape⟩ := callFrontend_declaration_sources declarations shapes (name,params,body) member
  simp only at eq
  rw [eq]
  exact callFrontend_simp_fixed shape

private theorem nested_zero_callScalar {width : Nat} [NeZero width] (names : List Nat)
    (body : CrepProgHOL width) (shape : SteppedFlapjack.CrepSteps.CallScalarProgram body) :
    SteppedFlapjack.CrepSteps.CallScalarProgram (nestedDecsHOL names (List.replicate names.length (.const (0 : BitVec width))) body) := by
  induction names with
  | nil => simpa [nestedDecsHOL] using shape
  | cons n ns ih =>
    simp only [List.length_cons,List.replicate_succ,nestedDecsHOL]
    exact .dec n (.direct (.const _)) ih

/-- The actual Pancake frontend produces call-aware Crep syntax. -/
theorem callFrontend_crepShape {width : Nat} [NeZero width]
    {ctxt : PanToCrepContextExact width} {p : ProgHOL width} (shape : CallFrontend ctxt p) :
    SteppedFlapjack.CrepSteps.CallScalarProgram (compileProgExactHOLW ctxt p) := by
  induction shape with
  | base h => exact .base (frontend_scalar_program h)
  | @tail ctxt fname args ha =>
    simpa only [compileProgExactHOLW,compileCallNoReturnExactHOLW,Option.map_none] using
      (SteppedFlapjack.CrepSteps.CallScalarProgram.call none fname ((compileExpExactHOLWList ctxt args).flatMap Prod.fst) (frontend_arguments_scalar ctxt args ha))
  | @decCall ctxt name sh fname args cont ha hb ih =>
    simp only [compileProgExactHOLW,compileDecCallExactHOLW]
    apply nested_zero_callScalar
    apply SteppedFlapjack.CrepSteps.CallScalarProgram.seq
    · exact .call (some _) fname _ (frontend_arguments_scalar ctxt args ha)
    · exact ih
  | @decl ctxt name e body he hb ih =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL]
    exact .dec _ scalar ih
  | @seq ctxt a b ha hb iha ihb => simpa only [compileProgExactHOLW] using SteppedFlapjack.CrepSteps.CallScalarProgram.seq iha ihb
  | @ite ctxt e a b he ha hb iha ihb =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp only [compileProgExactHOLW,compileIfExactHOLW,compiled]
    exact .ite scalar iha ihb
  | @«while» ctxt e body he hb ih =>
    obtain ⟨value,compiled,scalar⟩ := frontendScalar_compiled he
    simp only [compileProgExactHOLW,compileWhileExactHOLW,compiled]
    exact .loop scalar ih

/-- A Crep table compiled from call-aware source bodies has call-aware code. -/
theorem callFrontend_crepTable {width : Nat} [NeZero width]
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctxt : PanToCrepContextExact width) (p : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctxt p ∧ CallFrontend ctxt p) :
    SteppedFlapjack.CrepSteps.CallScalarTable (alistToFmapCodeExact programs) := by
  intro name params body found
  have member : (name,params,body) ∈ programs := by
    rw [alistToFmapCodeExact,HolFiniteMapExact.lookup_updateList] at found
    exact flookup_fupdateList_reverse_mem' programs name (params,body) found
  obtain ⟨ctxt,p,eq,shape⟩ := sources (name,params,body) member
  simp only at eq
  rw [eq]
  exact callFrontend_crepShape shape
/-- The generated Crep entry consumes no more clock than its actual visits,
including nested ordinary and tail calls into the generated function table. -/
theorem callFrontend_crep_clock_consumed {width : Nat} [NeZero width] {σ : Type}
    {ctxt : PanToCrepContextExact width} {p : ProgHOL width} (shape : CallFrontend ctxt p)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact width) (q : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (s : CrepSemHOLState width σ) (code : s.code = alistToFmapCodeExact programs) :
    s.clock - (evalCrepSemHOLProgExact s (compileProgExactHOLW ctxt p)).2.clock ≤
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW ctxt p) s := by
  apply SteppedFlapjack.CrepSteps.callScalarProgram_clock_consumed _ _ (callFrontend_crepShape shape)
  rw [code]
  exact callFrontend_crepTable programs sources


/-- The concrete frontend program list computes a uniform cost for every
compiled function body, independently of its compiler context. -/
theorem callFrontend_tableCost {width : Nat} [NeZero width]
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact width) (q : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (name : Flapjack.Basis.Pure.MlString.MlString) (params : List Nat) (body : CrepProgHOL width)
    (found : (alistToFmapCodeExact programs).lookup name = some (params,body))
    (ref ctxt : CrepToLoopContextExact) (live : NumSet) :
    loopVisitWeight (compileHOLExact ctxt live body) ≤
      callTableCost ref (programs.map (fun row => (row.2.1,row.2.2))) := by
  have member : (name,params,body) ∈ programs := by
    rw [alistToFmapCodeExact,HolFiniteMapExact.lookup_updateList] at found
    exact flookup_fupdateList_reverse_mem' programs name (params,body) found
  obtain ⟨ctx,q,compiled,shape⟩ := sources (name,params,body) member
  have bodyShape : SteppedFlapjack.CrepSteps.CallScalarProgram body := by
    change body = compileProgExactHOLW ctx q at compiled
    rw [compiled]
    exact callFrontend_crepShape shape
  have rowMember : (params,body) ∈ programs.map (fun row => (row.2.1,row.2.2)) := by
    exact List.mem_map.mpr ⟨(name,params,body),member,rfl⟩
  exact callScalar_tableCost ref ctxt live _ params body rowMember bodyShape

/-- Actual frontend output has explicit whole-table clock and Loop visit bounds. -/
theorem callFrontend_wholeVisits_explicit {width : Nat} [NeZero width] {σ : Type}
    (panCtxt : PanToCrepContextExact width) (p : ProgHOL width) (shape : CallFrontend panCtxt p)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (sources : ∀ row ∈ programs, ∃ (ctx : PanToCrepContextExact width) (q : ProgHOL width),
      row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q)
    (ref ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (sourceCode : source.code = alistToFmapCodeExact programs)
    (run : evalCrepSemHOLProgExact source (compileProgExactHOLW panCtxt p) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (nonTimeout : result ≠ some .timeOut)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code) (targetTable : LoopTableSupported target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let crep := compileProgExactHOLW panCtxt p
    let budget := callClockFactor ref rows source.clock crep * (CrepSteps.steps crep source+1)
    let factor := max (callSyntaxCost ref crep) (loopCodeWeight target.code+2)
    ∃ post, evaluate (compileHOLExact ctxt live crep) {target with clock := target.clock+budget} = (resultToLoop result,post) ∧
      LoopSteps.steps (compileHOLExact ctxt live crep) {target with clock := target.clock+budget} ≤
        callSyntaxCost ref crep + factor * (source.clock+budget) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧ localsResultRel ctxt live result sourceFinal post := by
  let rows := programs.map (fun row => (row.2.1,row.2.2))
  let crep := compileProgExactHOLW panCtxt p
  let budget := callClockFactor ref rows source.clock crep * (CrepSteps.steps crep source+1)
  let factor := max (callSyntaxCost ref crep) (loopCodeWeight target.code+2)
  have table : CrepSteps.CallScalarTable source.code := by
    rw [sourceCode]
    exact callFrontend_crepTable programs sources
  have cover : ∀ name params body, source.code.lookup name = some (params,body) →
      (params,body) ∈ programs.map (fun row => (row.2.1,row.2.2)) := by
    intro name params body found
    rw [sourceCode,alistToFmapCodeExact,HolFiniteMapExact.lookup_updateList] at found
    have member : (name,params,body) ∈ programs := flookup_fupdateList_reverse_mem' programs name (params,body) found
    exact List.mem_map.mpr ⟨(name,params,body),member,rfl⟩
  obtain ⟨post,ev,st,mem,gl,code,locals⟩ := callWholeClock_explicit ref ctxt live _ (fun _ => True) _ source sourceFinal result target
    (callFrontend_crepShape shape) table cover run nonerror nonTimeout stateRel memRel globalsRel codeRel trivial localsRel
  have weight := callScalar_syntaxCost (callFrontend_crepShape shape) ref ctxt live
  have weightFactor : loopVisitWeight (compileHOLExact ctxt live crep) ≤ factor :=
    weight.trans (Nat.le_max_left _ _)
  have loopBound := simpleSequence_global_bound (compileHOLExact ctxt live crep)
    {target with clock := target.clock+budget} factor (callFrontend_compiled_loopShape shape ctxt live)
    (by simpa using targetTable) (by simp [factor]) weightFactor
  rw [ev] at loopBound
  have used := Nat.mul_le_mul_left factor (Nat.sub_le (target.clock+budget) post.clock)
  have finalBound : LoopSteps.steps (compileHOLExact ctxt live crep) {target with clock := target.clock+budget} ≤
      callSyntaxCost ref crep + factor * (source.clock+budget) := by
    have targetClock := stateRel.2.2.1
    simp only at loopBound
    nlinarith
  exact ⟨post,ev,finalBound,st,mem,gl,code,locals⟩

/-- Compose source statements whose first part may call functions in the actual supported table. -/
theorem boundedCallSeq {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (source : CrepSemHOLState width σ) (factor : Nat) (positive : 1 ≤ factor)
    (shapeA : ∀ ctxt live, SimpleLoopSequenceSource (compileHOLExact ctxt live a))
    (first : BoundPropertyAt a source factor LoopTableSupported)
    (second : ∀ middle : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact source a = (none,middle) → BoundPropertyAt b middle factor LoopTableSupported) :
    BoundPropertyAt (.seq a b) source factor LoopTableSupported := by
  apply boundedSeq a b source factor positive LoopTableSupported ?_ first second
  intro ctxt live target middle extra table run
  exact loopTable_steps_add_clock (compileHOLExact ctxt live a) target middle none
    (shapeA ctxt live) table run (by simp) extra

end SteppedFlapjack.CrepToLoopSteps
