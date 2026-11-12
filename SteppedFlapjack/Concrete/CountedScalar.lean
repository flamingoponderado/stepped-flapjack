import SteppedFlapjack.Concrete.ScalarWords
import SteppedFlapjack.PanToCrepSteps.CountedInvert
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

/-- A successful counted scalar initializer supplies the HOL value and its
exact expression cost; scalar locals remain word-valued. -/
theorem counted_scalar_initializer_invert {σ : Type} {scope : List VarName}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (words : WordLocals production.locals)
    (initializer : Exp (RiscV.Word 64)) (scalar : Scalar scope initializer) (exprRanged : ExpByteRanged initializer)
    (value : PanValue (RiscV.Word 64)) (cost : Nat)
    (run : panValueDecAccepted production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
      production.locals production.globals production.memory initializer
      (some (panSemBitVec64MemoryAccess production)) .one = some (value,cost)) :
    ∃ word, value = .word word ∧ cost = panValueExpStepCost initializer ∧
      @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
        (expToHOL initializer) = some (.val (.word word)) := by
  simp only [panValueDecAccepted,evalPanValueExpCounted] at run
  cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord initializer
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
  | none => simp [evaluated] at run
  | some result =>
    simp only [evaluated,Option.map_some] at run
    split at run
    · simp only [Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      have expressionRun : evalPanSemStateExp production initializer = some result := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words result expressionRun
      exact ⟨word,rfl,rfl,(counted_condition_word production source rel ranged initializer exprRanged word expressionRun).2⟩
    · simp at run
/-- A counted scalar return carries a word, clears locals, and has the
corresponding HOL result and state. -/
theorem counted_scalar_return_invert {σ : Type} {scope : List VarName}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (words : WordLocals production.locals)
    (expression : Exp (RiscV.Word 64)) (scalar : Scalar scope expression) (exprRanged : ExpByteRanged expression)
    (value : PanValue (RiscV.Word 64)) (postLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.return expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned postLocals production.globals production.memory production.ffi [value],count)) :
    ∃ word, value = .word word ∧ postLocals = (fun _ => none) ∧
      source.evaluateHOLFiniteState (.return (expToHOL expression)) =
        (some (.returned (.val (.word word))),source.emptyLocalsHOLFinite) ∧
      PanSemStateRelExec (panEmptyLocals production) source.emptyLocalsHOLFinite.toExact ∧
      PanSemStateRelExecRanged (panEmptyLocals production) ∧
      controlSteps (.return (expToHOL expression)) source ≤ count := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    have originalRun := run
    simp only [evalPanValueFfiProgSteps,panValueReturnResult,
      evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => simp [evaluated] at run
    | some result =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq,PanValueFfiControlResult.returned.injEq,List.cons.injEq,
          and_true,true_and] at run
        obtain ⟨⟨localsEq,valueEq⟩,costEq⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some result := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,resultEq⟩ := scalar_eval_word scalar production words result expressionRun
        have valueWord : value = .word word := valueEq.symm.trans resultEq
        subst postLocals
        have originalRun' : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
            production.locals production.globals production.memory production.ffi (.return expression)
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
              some (.returned (fun _ => none) production.globals production.memory production.ffi [.word word],count) := by
          simpa [valueWord] using originalRun
        have inverted := counted_return_invert production source rel ranged expression exprRanged word
          context primitive handler functions (fuel+1) count originalRun'
        exact ⟨word,valueWord,rfl,inverted⟩
      · simp at run

/-- Related source states agree when evaluating a byte-ranged expression fails. -/
theorem source_expression_error {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (expression : Exp (RiscV.Word 64))
    (exprRanged : ExpByteRanged expression) (failed : evalPanSemStateExp production expression = none) :
    @evalHOLExact 64 σ _ source.toExact (fun address => Classical.propDecidable (source.memaddrs address))
      (expToHOL expression) = none := by
  have agree := evalPanSemStateExp_agree production source rel ranged expression exprRanged
  rw [evalHOLFinite_eq_classical,← agree,failed]
  rfl

/-- An erroneous scalar return has zero counted source steps when its
expression fails. HOL reports the same error in the same state, but visits
one statement, so source-error bounds must allow this extra visit. -/
theorem counted_scalar_return_error {σ : Type} {scope : List VarName}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (expression : Exp (RiscV.Word 64)) (scalar : Scalar scope expression) (exprRanged : ExpByteRanged expression)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.return expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.error production.locals production.globals production.memory production.ffi,count)) :
    count = 0 ∧ source.evaluateHOLFiniteState (.return (expToHOL expression)) = (some .error,source) ∧
      controlSteps (.return (expToHOL expression)) source = 1 := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,panValueReturnResult,evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none =>
      simp [evaluated] at run
      subst count
      have evalNone : evalPanSemStateExp production expression = none := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      have exactNone := source_expression_error production source rel ranged expression exprRanged evalNone
      refine ⟨rfl,?_,?_⟩
      · rw [evaluateHOLFiniteState_return,exactNone]
      · rw [controlSteps.eq_def]
        rfl
    | some value =>
      have expressionRun : evalPanSemStateExp production expression = some value := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
      simp [evaluated] at run

/-- A failed scalar condition also fails in the HOL source evaluator. -/
theorem counted_scalar_condition_error {σ : Type} {scope : List VarName}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (expression : Exp (RiscV.Word 64)) (scalar : Scalar scope expression) (exprRanged : ExpByteRanged expression)
    (failed : panValueIteCondition production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
      production.locals production.globals production.memory expression (some (panSemBitVec64MemoryAccess production)) = none) :
    @evalHOLExact 64 σ _ source.toExact (fun address => Classical.propDecidable (source.memaddrs address))
      (expToHOL expression) = none := by
  have none : evalPanSemStateExp production expression = none := by
    rw [evalPanSemStateExp_64_eq_previous]
    simp only [panValueIteCondition,evalPanValueExpCounted] at failed
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => rfl
    | some value =>
      have expressionRun : evalPanSemStateExp production expression = some value := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
      simp [evaluated] at failed
  exact source_expression_error production source rel ranged expression exprRanged none

/-- A rejected scalar declaration initializer also fails in the HOL source evaluator. -/
theorem counted_scalar_initializer_error {σ : Type} {scope : List VarName}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (expression : Exp (RiscV.Word 64)) (scalar : Scalar scope expression) (exprRanged : ExpByteRanged expression)
    (failed : panValueDecAccepted production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
      production.locals production.globals production.memory expression (some (panSemBitVec64MemoryAccess production)) .one = none) :
    @evalHOLExact 64 σ _ source.toExact (fun address => Classical.propDecidable (source.memaddrs address))
      (expToHOL expression) = none := by
  have none : evalPanSemStateExp production expression = none := by
    rw [evalPanSemStateExp_64_eq_previous]
    simp only [panValueDecAccepted,evalPanValueExpCounted] at failed
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => rfl
    | some value =>
      have expressionRun : evalPanSemStateExp production expression = some value := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
      simp [evaluated,panValueShape,panShapeMatches] at failed
  exact source_expression_error production source rel ranged expression exprRanged none

/-- A counted local-assignment error agrees with HOL, including failures
of either expression evaluation or assignment validity. -/
theorem counted_assign_error {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (name : VarName) (nameRanged : NameRanged name)
    (expression : Exp (RiscV.Word 64)) (exprRanged : ExpByteRanged expression)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.assign .local name expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.error production.locals production.globals production.memory production.ffi,count)) :
    source.evaluateHOLFiniteState (.assign .local (ofString name) (expToHOL expression)) = (some .error,source) ∧
      controlSteps (.assign .local (ofString name) (expToHOL expression)) source = 1 := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,panValueAssignLocalResult,evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none =>
      have evalNone : evalPanSemStateExp production expression = none := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      have exactNone := source_expression_error production source rel ranged expression exprRanged evalNone
      constructor
      · rw [evaluateHOLFiniteState_assign,exactNone]
      · rw [controlSteps.eq_def]; rfl
    | some value =>
      have evalSome : evalPanSemStateExp production expression = some value := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp at run
      · rename_i invalid
        have rangedValue := evalPanSemStateExp_byteRanged production ranged expression exprRanged value evalSome
        have agree := evalPanSemStateExp_agree production source rel ranged expression exprRanged
        have exactSome : @evalHOLExact 64 σ _ source.toExact
            (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL expression) =
              some (panValueToHOL value) := by
          rw [evalHOLFinite_eq_classical,← agree,evalSome]
          rfl
        have parity := panValueAssignmentValid_eq_isValidValueHOLFinite production source rel ranged .local name nameRanged value rangedValue
        have invalidExact : isValidValueHOLFinite source .local (ofString name) (panValueToHOL value) = false := by
          rw [← parity]
          exact Bool.eq_false_iff.mpr invalid
        rw [isValidValueHOLFinite_eq] at invalidExact
        constructor
        · rw [evaluateHOLFiniteState_assign,exactSome]
          simp [invalidExact]
        · rw [controlSteps.eq_def]; rfl
/-- An erroneous global assignment agrees with the HOL evaluator and visits one statement. -/
theorem counted_assign_global_error {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (name : VarName) (nameRanged : NameRanged name)
    (expression : Exp (RiscV.Word 64)) (exprRanged : ExpByteRanged expression)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.assign .global name expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.error production.locals production.globals production.memory production.ffi,count)) :
    source.evaluateHOLFiniteState (.assign .global (ofString name) (expToHOL expression)) = (some .error,source) ∧
      controlSteps (.assign .global (ofString name) (expToHOL expression)) source = 1 := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,panValueAssignGlobalResult,evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none =>
      have evalNone : evalPanSemStateExp production expression = none := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      have exactNone := source_expression_error production source rel ranged expression exprRanged evalNone
      constructor
      · rw [evaluateHOLFiniteState_assign,exactNone]
      · rw [controlSteps.eq_def]; rfl
    | some value =>
      have evalSome : evalPanSemStateExp production expression = some value := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp at run
      · rename_i invalid
        have rangedValue := evalPanSemStateExp_byteRanged production ranged expression exprRanged value evalSome
        have agree := evalPanSemStateExp_agree production source rel ranged expression exprRanged
        have exactSome : @evalHOLExact 64 σ _ source.toExact
            (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL expression) =
              some (panValueToHOL value) := by
          rw [evalHOLFinite_eq_classical,← agree,evalSome]
          rfl
        have parity := panValueAssignmentValid_eq_isValidValueHOLFinite production source rel ranged .global name nameRanged value rangedValue
        have invalidExact : isValidValueHOLFinite source .global (ofString name) (panValueToHOL value) = false := by
          rw [← parity]
          exact Bool.eq_false_iff.mpr invalid
        rw [isValidValueHOLFinite_eq] at invalidExact
        constructor
        · rw [evaluateHOLFiniteState_assign,exactSome]
          simp [invalidExact]
        · rw [controlSteps.eq_def]; rfl

end SteppedFlapjack.Concrete
