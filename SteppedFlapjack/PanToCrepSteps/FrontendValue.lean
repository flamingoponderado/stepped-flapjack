import SteppedFlapjack.PanToCrepSteps.FrontendScalar
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- A scalar or recursively nested tuple of scalar expressions. -/
inductive FrontendValue {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) : ExpHOL width → Prop
  | scalar {e} : FrontendScalar ctxt e → FrontendValue ctxt e
  | tuple {fields} : (∀ e ∈ fields, FrontendValue ctxt e) → FrontendValue ctxt (.rstruct fields)

private theorem shapeListSize {width : Nat} [NeZero width] (items : List (List (CrepExpHOL width) × ShapeHOL))
    (h : ∀ item ∈ items, sizeOfShapeHOL item.2 = item.1.length) :
    sizeOfShapesHOL (items.map Prod.snd) = (items.flatMap Prod.fst).length := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    simp only [List.map_cons,sizeOfShapesHOL,List.flatMap_cons,List.length_append]
    rw [h item (by simp),ih (by intro v hv; exact h v (by simp [hv]))]

theorem frontend_compileList_map {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (fields : List (ExpHOL width)) : compileExpExactHOLWList ctxt fields = fields.map (compileExpExactHOLW ctxt) := by
  induction fields with
  | nil => simp [compileExpExactHOLWList]
  | cons e es ih => simp [compileExpExactHOLWList,ih]

theorem frontendValue_compile {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (h : FrontendValue ctxt e) :
    ∃ values sh, compileExpExactHOLW ctxt e = (values,sh) ∧ sizeOfShapeHOL sh = values.length := by
  induction h with
  | scalar h =>
    obtain ⟨value,compiled⟩ := frontendScalar_compile h
    exact ⟨[value],.one,compiled,by simp [sizeOfShapeHOL]⟩
  | @tuple fields hs ih =>
    let items := compileExpExactHOLWList ctxt fields
    have each : ∀ item ∈ items, sizeOfShapeHOL item.2 = item.1.length := by
      intro item member
      have mapped : items = fields.map (compileExpExactHOLW ctxt) := frontend_compileList_map ctxt fields
      rw [mapped,List.mem_map] at member
      obtain ⟨field,fieldMem,rfl⟩ := member
      obtain ⟨values,sh,compiled,sz⟩ := ih field fieldMem
      rw [compiled]
      exact sz
    refine ⟨items.flatMap Prod.fst,.comb (items.map Prod.snd),?_,?_⟩
    · simp [compileExpExactHOLW,items]
    · exact shapeListSize items each
theorem frontendValue_localised {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (h : FrontendValue ctxt e) : localisedExpHOL e = true := by
  induction h with
  | scalar h => exact frontendScalar_localised h
  | @tuple fields hs ih =>
    simp only [localisedExpHOL,everyExpHOL,Bool.true_and]
    induction fields with
    | nil => rfl
    | cons e es rec =>
      simp only [everyExpListHOL,Bool.and_eq_true]
      exact ⟨ih e (by simp),rec (fun x hx => hs x (by simp [hx])) (fun x hx => ih x (by simp [hx]))⟩

/-- A two-level struct is accepted and its scalar leaves retain their order. -/
theorem nestedStruct_frontend_example {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (a b c : BitVec width) :
    FrontendValue ctxt (.rstruct [.rstruct [.const a,.const b],.const c]) ∧
      compileExpExactHOLW ctxt (.rstruct [.rstruct [.const a,.const b],.const c]) =
        ([.const a,.const b,.const c],.comb [.comb [.one,.one],.one]) := by
  constructor
  · apply FrontendValue.tuple
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · apply FrontendValue.tuple
      intro e member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> exact .scalar (.const _)
    · exact .scalar (.const _)
  · simp [compileExpExactHOLW,compileExpExactHOLWList]

end SteppedFlapjack.PanToCrepSteps
