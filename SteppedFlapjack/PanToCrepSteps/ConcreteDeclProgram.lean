import SteppedFlapjack.PanToCrepSteps.CountedDeclExample
import SteppedFlapjack.PanToCrepSteps.OriginalDeclEntryRiscV

/-! Concrete original source and its machine-theorem inputs. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A closed, zero-argument Pancake body that initializes a local, executes
one state-changing loop iteration, and returns a constant. -/
def concreteDeclBody (name : VarName) (returned : BitVec 64) : ProgHOL 64 :=
  .dec (ofString name) .one (.const 1)
    (.seq .skip (.seq (.while (.var .local (ofString name)) (.assign .local (ofString name) (.const 0)))
      (.return (.const returned))))

/-- One non-inlined zero-argument function containing the concrete body. -/
def concreteDeclProgram (start : MlString) (name : VarName) (returned : BitVec 64) : List (DeclHOL 64) :=
  [.function ⟨start,false,false,[],concreteDeclBody name returned,.one⟩]

/-- The original function table contains the exact zero-argument body. -/
theorem concreteDeclProgram_lookup (start : MlString) (name : VarName) (returned : BitVec 64) :
    (functionsHOL (concreteDeclProgram start name returned)).lookup start =
      some ([],concreteDeclBody name returned,.one) := by
  simp [concreteDeclProgram,functionsHOL]

/-- The counted source execution supplies the original-entry machine theorem's
run, source limit, source syntax shapes, and actual function-table lookup. -/
theorem concreteDecl_source_inputs {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (clock : source.clock ≠ 0)
    (returned : BitVec 64) (caller : PanToCrepContextExact 64) (start : MlString)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let c := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let inner := scalarDeclContext c (ofString name)
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+7)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const 1) (.seq .skip (.seq (.while (.var .local name)
          (.assign .local name (.const 0))) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,13) ∧
      source.evaluateHOLFiniteState (concreteDeclBody name returned) =
        (some (.returned (.val (.word returned))),final) ∧
      controlSteps (concreteDeclBody name returned) source ≤ 13 ∧
      ScalarExpression c (.const 1) ∧ BranchProgram inner .skip ∧
      ScalarExpression inner (.var .local (ofString name)) ∧
      BranchProgram inner (.assign .local (ofString name) (.const 0)) ∧
      BranchProgram inner (.return (.const returned)) ∧
      (functionsHOL (concreteDeclProgram start name returned)).lookup start =
        some ([],concreteDeclBody name returned,.one) ∧
      SteppedFlapjack.CrepToLoopSteps.SupportedCodeBody (compileProgExactHOLW c (concreteDeclBody name returned)) := by
  obtain ⟨result,final,exec,run,bound,supported⟩ := counted_decl_set_zero_with_tail production source rel ranged
    name nameRanged clock returned (ctxtFcExactHOL caller.funcs caller.eids [] [] []) context primitive handler functions fuel
  have found := scalarDeclContext_local (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name)
  refine ⟨result,final,exec,?_,?_,.const _,.skip,.local _ _ found,.assign _ _ found (.const _),
    .return (.const _),concreteDeclProgram_lookup start name returned,?_⟩
  · simpa only [concreteDeclBody] using run
  · simpa only [concreteDeclBody] using bound
  · simpa only [concreteDeclBody] using supported

/-- For the concrete program, the counted execution directly supplies the
original source run and the generated global-entry visit bound. -/
theorem concreteDecl_globalEntry_inputs {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (sourceClock : source.clock ≠ 0)
    (returned : BitVec 64) (start : MlString) (caller : PanToCrepContextExact 64)
    (initializers : List (ProgHOL 64)) (globals : PanGlobalsContextExact 64)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (newMainNameHOL (concreteDeclProgram start name returned),([],concreteDeclBody name returned,.one)))
    (clock : middle.clock ≠ 0)
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    ∃ result sourceFinal loweredFinal,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+7)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const 1) (.seq .skip (.seq (.while (.var .local name)
          (.assign .local name (.const 0))) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,13) ∧
      source.evaluateHOLFiniteState (concreteDeclBody name returned) =
        (some (.returned (.val (.word returned))),sourceFinal) ∧
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty).evaluateHOLFiniteState
        (compileProgExactHOL globals (concreteDeclBody name returned)) =
        (some (.returned (.val (.word returned))),loweredFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal loweredFinal ∧
      globalEntrySteps (nestedSeqHOL initializers) (newMainNameHOL (concreteDeclProgram start name returned)) [] pan ≤
        controlSteps (nestedSeqHOL initializers) pan +
          (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
            sizeOf (compileProgExactHOL globals (.assign .local (ofString name) (.const 0))) +
            sizeOf (compileProgExactHOL globals (.return (.const returned)))) * 13 + 2 := by
  obtain ⟨result,sourceFinal,exec,run,bound,_,initShape,_,bodyShape,tailShape,_,_⟩ :=
    concreteDecl_source_inputs production source rel ranged name nameRanged sourceClock returned caller start
      context primitive handler functions fuel
  have sourceFound : source.code.lookup (newMainNameHOL (concreteDeclProgram start name returned)) =
      some ([],concreteDeclBody name returned,.one) := by
    rw [sourceCode]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨loweredFinal,_,loweredRun,postRel,entryBound⟩ := globalEntry_originalDeclLoop_with_steps
    (concreteDeclProgram start name returned) start initializers globals
    (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name))
    (ofString name) (.const 1) .skip (.var .local (ofString name))
    (.assign .local (ofString name) (.const 0)) (.return (.const returned))
    initShape bodyShape tailShape pan middle source sourceFinal (some (.returned (.val (.word returned)))) .one
    panCode initRun (by simpa only [concreteDeclBody] using sourceFound) clock
    (by simpa only [concreteDeclBody] using run) (by simp) globalRel
  refine ⟨result,sourceFinal,loweredFinal,exec,run,?_,postRel,?_⟩
  · simpa only [concreteDeclBody] using loweredRun
  · have scaled := Nat.mul_le_mul_left
      (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
        sizeOf (compileProgExactHOL globals (.assign .local (ofString name) (.const 0))) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) bound
    simp only [concreteDeclBody] at scaled
    omega

end SteppedFlapjack.PanToCrepSteps
