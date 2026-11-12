import SteppedFlapjack.Concrete.CountedScalar
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

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

end SteppedFlapjack.Concrete
