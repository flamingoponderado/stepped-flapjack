import SteppedFlapjack.Concrete.CountedScalar
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

def GlobalHOLShapes (shapes : VarName → Option ShapeHOL)
    (globals : VarName → Option (PanValue (RiscV.Word 64))) : Prop :=
  ∀ name, NameRanged name → (globals name).map (fun v => shapeOfHOLExact (panValueToHOL v)) = shapes name

theorem globalShapeMap_run {σ : Type} (source final : PanSemStateFiniteExact 64 σ)
    (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState program = (result,final)) : globalsShapes final = globalsShapes source := by
  classical
  let context : FiniteEvalContext 64 σ := ⟨source, (fun a => Classical.propDecidable (source.memaddrs a)),
    (fun a => Classical.propDecidable (source.shMemaddrs a))⟩
  obtain ⟨post, heval, hstate⟩ := evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState source program context rfl
      (result,final) run
  have h := evalPanSemRecursiveCallFiniteContext_globalsShapesInvariant program context result post heval
  rw [hstate] at h
  exact h

theorem globalHOLShapes_transport {σ : Type}
    (production next : PanSemState (RiscV.Word 64) (FfiState σ))
    (source final : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (nextRel : PanSemStateRelExec next final.toExact)
    (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState program = (result,final))
    (shapes : VarName → Option ShapeHOL) (valid : GlobalHOLShapes shapes production.globals) :
    GlobalHOLShapes shapes next.globals := by
  intro name ranged
  have before := rel.2.1 name ranged
  have after := nextRel.2.1 name ranged
  have hshape := valid name ranged
  cases hg : production.globals name with
  | none =>
    simp only [hg,Option.map_none] at before hshape
    have inv := congrFun (globalShapeMap_run source final program result run) (ofString name)
    simp only [globalsShapes] at inv
    rw [← before] at inv
    simp only [Option.map_none] at inv
    cases hn : next.globals name with
    | none => simp [hshape]
    | some value =>
      simp only [hn, Option.map_some] at after
      rw [← after] at inv
      simp at inv
  | some value =>
    simp only [hg,Option.map_some] at before hshape
    have lookup : source.globals.lookup (ofString name) = some (panValueToHOL value) := before.symm
    obtain ⟨new, found, shape⟩ := evaluateHOLFiniteState_global_shape_invariant source program result final
      (ofString name) (panValueToHOL value) run lookup
    cases hn : next.globals name with
    | none => simp [hn,found] at after
    | some v =>
      simp only [hn,Option.map_some] at after ⊢
      rw [found,Option.some.injEq] at after
      rw [after,shape,hshape]
/-- Selecting a field from a value selects the corresponding static shape. -/
theorem shape_of_rfield (fields : List (PanValue (RiscV.Word 64)))
    (shapes : List ShapeHOL) (index : Nat) (value : PanValue (RiscV.Word 64))
    (shape : ShapeHOL) (hshape : shapeOfHOLExact (panValueToHOL (.rStruct fields)) = .comb shapes)
    (hfield : fields[index]? = some value) (hselect : shapes[index]? = some shape) :
    shapeOfHOLExact (panValueToHOL value) = shape := by
  simp only [panValueToHOL,shapeOfHOLExact,ShapeHOL.comb.injEq] at hshape
  subst shapes
  simpa [hfield] using hselect

inductive GlobalRead (shapes : VarName → Option ShapeHOL) : Exp (RiscV.Word 64) → ShapeHOL → Prop
  | global (name : VarName) (shape : ShapeHOL) : NameRanged name → shapes name = some shape → GlobalRead shapes (.var .global name) shape
  | field {e fields} (path : GlobalRead shapes e (.comb fields)) (index : Nat) (shape : ShapeHOL)
      (found : fields[index]? = some shape) : GlobalRead shapes (.rField index e) shape

theorem globalRead_shape {σ : Type} {shapes : VarName → Option ShapeHOL} {e : Exp (RiscV.Word 64)} {shape : ShapeHOL}
    (read : GlobalRead shapes e shape) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (valid : GlobalHOLShapes shapes production.globals) (value : PanValue (RiscV.Word 64))
    (evaluated : evalPanSemStateExp production e = some value) : shapeOfHOLExact (panValueToHOL value) = shape := by
  rw [evalPanSemStateExp_64_eq_previous] at evaluated
  induction read generalizing value with
  | global name shape ranged found =>
    simp only [evalPanValueExp] at evaluated
    have h := valid name ranged
    rw [evaluated, found] at h
    simpa using h
  | @field e fields path index shape found ih =>
    simp only [evalPanValueExp] at evaluated
    cases he : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord e
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => simp [he] at evaluated
    | some parent =>
      have parentShape := ih parent he
      cases parent with
      | word w => simp [he] at evaluated
      | nStruct name fields => simp [he] at evaluated
      | rStruct fields =>
        simp only [he] at evaluated
        exact shape_of_rfield fields _ index value shape parentShape evaluated found

theorem globalRead_word {σ : Type} {shapes : VarName → Option ShapeHOL} {e : Exp (RiscV.Word 64)}
    (read : GlobalRead shapes e .one) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (valid : GlobalHOLShapes shapes production.globals) (value : PanValue (RiscV.Word 64))
    (evaluated : evalPanSemStateExp production e = some value) : ∃ word, value = .word word := by
  have h := globalRead_shape read production valid value evaluated
  cases value with
  | word w => exact ⟨w,rfl⟩
  | rStruct fields => simp [shapeOfHOLExact] at h
  | nStruct name fields => simp [shapeOfHOLExact] at h

theorem flatList_one_word {α : Type} [BEq α] [Add α]
    (structs : StructContext) (readWord : α → Option α) (bytes : α) :
    ∀ (fuel : Nat) (shapes : List Shape) (address : α) (values : List (PanValue α)) (index : Nat) (value : PanValue α),
      panValueFlatLoadListFuel structs readWord bytes fuel shapes address = some values →
      shapes[index]? = some .one → values[index]? = some value →
      ∃ word, value = .word word := by
  intro fuel
  induction fuel with
  | zero =>
    intro shapes address values index value loaded selected got
    cases shapes <;> simp [panValueFlatLoadListFuel] at loaded
    subst values
    simp at got
  | succ fuel ih =>
    intro shapes address values index value loaded selected got
    cases shapes with
    | nil =>
      simp [panValueFlatLoadListFuel] at loaded
      subst values
      simp at got
    | cons shape shapes =>
      cases hv : panValueFlatLoadFuel structs readWord bytes fuel shape address with
      | none => simp [panValueFlatLoadListFuel, hv] at loaded
      | some head =>
        cases ht : panValueFlatLoadListFuel structs readWord bytes fuel shapes
            (panValueFlatOffset bytes address (shapeSizeWithContext structs shape)) with
        | none => simp [panValueFlatLoadListFuel, hv, ht] at loaded
        | some tail =>
          simp [panValueFlatLoadListFuel, hv, ht] at loaded
          subst values
          cases index with
          | zero =>
            simp at selected got
            subst shape
            subst value
            cases fuel with
            | zero => simp [panValueFlatLoadFuel] at hv
            | succ fuel =>
              cases hw : readWord address with
              | none => simp [panValueFlatLoadFuel, hw] at hv
              | some word =>
                simp [panValueFlatLoadFuel, hw] at hv
                exact ⟨word,hv.symm⟩
          | succ index =>
            exact ih shapes _ tail index value ht (by simpa using selected) (by simpa using got)

/-- Global-aware scalar expressions retain word-valued successful evaluations. -/
inductive GlobalScalarExpression (shapes : VarName → Option ShapeHOL) (scope : List VarName) : Exp (RiscV.Word 64) → Prop
  | local {e} : Scalar scope e → GlobalScalarExpression shapes scope e
  | global {e} : GlobalRead shapes e .one → GlobalScalarExpression shapes scope e
  | load {address} : GlobalScalarExpression shapes scope address → GlobalScalarExpression shapes scope (.load .one address)
  | heapField (fields : List Shape) (index : Nat) : fields[index]? = some .one →
      ∀ {address}, GlobalScalarExpression shapes scope address →
      GlobalScalarExpression shapes scope (.rField index (.load (.comb fields) address))
  | op (operator) {a b} : GlobalScalarExpression shapes scope a → GlobalScalarExpression shapes scope b → GlobalScalarExpression shapes scope (.op operator [a,b])
  | cmp (operator) {a b} : GlobalScalarExpression shapes scope a → GlobalScalarExpression shapes scope b → GlobalScalarExpression shapes scope (.cmp operator a b)
  | shift (operator) {a b} : GlobalScalarExpression shapes scope a → GlobalScalarExpression shapes scope b → GlobalScalarExpression shapes scope (.shift operator a b)

/-- Values with scalar leaves and recursively nested anonymous structs. -/
inductive GlobalValueExpression (shapes : VarName → Option ShapeHOL) (scope : List VarName) : Exp (RiscV.Word 64) → Prop
  | scalar {e} : GlobalScalarExpression shapes scope e → GlobalValueExpression shapes scope e
  | tuple {fields} : (∀ e ∈ fields, GlobalValueExpression shapes scope e) →
      GlobalValueExpression shapes scope (.rStruct fields)

theorem globalScalarExpression_word {σ : Type} {shapes : VarName → Option ShapeHOL} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : GlobalScalarExpression shapes scope expression) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (words : ScopedWordLocals scope production.locals) (globals : GlobalHOLShapes shapes production.globals)
    (value : PanValue (RiscV.Word 64)) (evaluated : evalPanSemStateExp production expression = some value) : ∃ word, value = .word word := by
  rw [evalPanSemStateExp_64_eq_previous] at evaluated
  induction scalar generalizing value with
  | «local» h => apply scalar_eval_word_scoped h production words value; simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
  | global h => apply globalRead_word h production globals value; simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
  | @load address ha ih =>
    simp only [evalPanValueExp] at evaluated
    cases addressRun : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord address
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [addressRun] at evaluated
    | some result =>
      obtain ⟨addressWord,rfl⟩ := ih result addressRun
      cases read : panValueFlatReadWord production.memory panSemBitVec64BytesInWord
          (some (panSemBitVec64MemoryAccess production)) addressWord with
      | none => simp [addressRun,panValueFlatLoad,isWfShape,panValueFlatLoadFuel,read] at evaluated
      | some word =>
        simp [addressRun,panValueFlatLoad,isWfShape,panValueFlatLoadFuel,read] at evaluated
        subst value
        exact ⟨word,rfl⟩
  | @heapField fields index selected address ha ih =>
    simp only [evalPanValueExp] at evaluated
    cases addressRun : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord address
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [addressRun] at evaluated
    | some result =>
      obtain ⟨addressWord,rfl⟩ := ih result addressRun
      simp only [addressRun] at evaluated
      unfold panValueFlatLoad at evaluated
      split at evaluated
      · cases fuelEq : panValueFlatContextFuel production.structs + panValueFlatShapeFuel (.comb fields) + 1 with
        | zero => simp [fuelEq,panValueFlatLoadFuel] at evaluated
        | succ fuel =>
          cases loaded : panValueFlatLoadListFuel production.structs
              (panValueFlatReadWord production.memory panSemBitVec64BytesInWord
                (some (panSemBitVec64MemoryAccess production))) panSemBitVec64BytesInWord
              fuel fields addressWord with
          | none => simp [fuelEq,panValueFlatLoadFuel,loaded] at evaluated
          | some values =>
            simp [fuelEq,panValueFlatLoadFuel,loaded] at evaluated
            exact flatList_one_word production.structs _ _ fuel fields addressWord values index value loaded selected evaluated
      · simp at evaluated
  | @op operator a b ha hb iha ihb =>
    simp only [evalPanValueExp] at evaluated
    cases argsRun : evalPanValueExp.evalPanValueExps production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord [a,b]
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [argsRun] at evaluated
    | some values =>
      cases projected : values.mapM panValueWordProjection with
      | none => simp [argsRun,projected] at evaluated
      | some nums =>
        cases opRun : (panSemBitVec64MemoryAccess production).wordOp operator nums with
        | none => simp [argsRun,projected,opRun] at evaluated
        | some w =>
          simp [argsRun,projected,opRun] at evaluated
          subst value
          exact ⟨w,rfl⟩
  | @cmp operator a b ha hb iha ihb =>
    simp only [evalPanValueExp] at evaluated
    cases leftRun : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord a
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [leftRun] at evaluated
    | some left =>
      cases rightRun : evalPanValueExp production.structs production.locals production.globals production.memory
          production.baseAddress production.topAddress panSemBitVec64BytesInWord b
          (some (panSemBitVec64MemoryAccess production)) with
      | none => simp [leftRun,rightRun] at evaluated
      | some right =>
        obtain ⟨leftWord,rfl⟩ := iha left leftRun
        obtain ⟨rightWord,rfl⟩ := ihb right rightRun
        simp [leftRun,rightRun] at evaluated
        subst value
        exact ⟨_,rfl⟩
  | @shift operator a b ha hb iha ihb =>
    simp only [evalPanValueExp] at evaluated
    cases leftRun : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord a
        (some (panSemBitVec64MemoryAccess production)) with
    | none => simp [leftRun] at evaluated
    | some left =>
      cases rightRun : evalPanValueExp production.structs production.locals production.globals production.memory
          production.baseAddress production.topAddress panSemBitVec64BytesInWord b
          (some (panSemBitVec64MemoryAccess production)) with
      | none => simp [leftRun,rightRun] at evaluated
      | some right =>
        obtain ⟨leftWord,rfl⟩ := iha left leftRun
        obtain ⟨rightWord,rfl⟩ := ihb right rightRun
        cases shiftRun : (panSemBitVec64MemoryAccess production).shift operator leftWord rightWord with
        | none => simp [leftRun,rightRun,shiftRun] at evaluated
        | some word =>
          simp [leftRun,rightRun,shiftRun] at evaluated
          subst value
          exact ⟨word,rfl⟩


/-- Counted returns admit typed global scalar expressions. -/
theorem counted_global_scalar_return_invert {σ : Type} {scope : List VarName} {shapes : VarName → Option ShapeHOL}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (words : WordLocals production.locals) (globals : GlobalHOLShapes shapes production.globals)
    (expression : Exp (RiscV.Word 64)) (scalar : GlobalScalarExpression shapes scope expression) (exprRanged : ExpByteRanged expression)
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
  exact counted_word_return_invert production source rel ranged expression
    (fun value evaluated => globalScalarExpression_word scalar production words.scoped globals value evaluated)
    exprRanged value postLocals context primitive handler functions fuel count run

end SteppedFlapjack.Concrete
