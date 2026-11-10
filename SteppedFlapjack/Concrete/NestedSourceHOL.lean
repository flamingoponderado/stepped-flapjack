import SteppedFlapjack.Concrete.NestedCalls
import SteppedFlapjack.Concrete.Phase7SourceClock
import SteppedFlapjack.PanToCrepSteps.WhileSteps

/-! Original HOL-shaped source execution for the nested-call witness. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

def nestedSourceState : PanSemStateFiniteExact 64 Unit :=
  let mainCode := sourceTemplate.code.update (ofString "main", ([], progToHOL nestedCallEntry, .one))
  let middleCode := mainCode.update (ofString "middle", ([], .call none (ofString "leaf") [], .one))
  let allCode := middleCode.update (ofString "leaf", ([], .return (.const 7), .one))
  {sourceTemplate with code := allCode}

/-- Observational semantics starts from the original empty declaration state. -/
theorem nestedCall_declared_semantics :
    semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
      (nestedCallDeclarations.map declToHOL) = semantics nestedSourceState (ofString "main") := by
  have same : semantics {nestedSourceState with clock := 0} (ofString "main") =
      semantics nestedSourceState (ofString "main") := by
    cases nestedSourceState
    rfl
  simpa [semanticsDecls,nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,
    progToHOL,expToHOL,shapeToHOL,decsStcnamesHOLExact,evaluateDeclsHOLFinite,
    nestedSourceState,sourceTemplate,isWfShapeExactHOL] using same

/-- The original source entry returns the witness value with unchanged FFI. -/
theorem nestedCall_hol_run :
    ∃ final, evaluateHOLFiniteState {nestedSourceState with clock := 4}
      (.call none (ofString "main") []) =
      (some (.returned (.val (.word 7))),final) ∧ final.ffi = sourceFfi := by
  have leafMain : (ofString "leaf" == ofString "main") = false := by decide
  have middleMain : (ofString "middle" == ofString "main") = false := by decide
  have leafMiddle : (ofString "leaf" == ofString "middle") = false := by decide
  simp [leafMain,middleMain,leafMiddle,evaluateHOLFiniteState_call,nestedSourceState,nestedCallEntry,progToHOL,
    expToHOL,shapeToHOL,sourceTemplate,evalListHOLFinite,evalListHOLExact,
    PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,HolFiniteMapExact.lookup_update,FUPDATE,
    evaluateHOLFiniteState_decCall_fixClockRewrite,evaluateHOLFiniteState_return,callEntryStateHOLFinite,
    evalHOLExact,shapeOfHOLExact,shapeEqHOL,setVarHOLFinite,emptyLocalsHOLFinite]

/-- The original declarations terminate successfully without I/O events. -/
theorem nestedCall_source_semantics :
    semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
      (nestedCallDeclarations.map declToHOL) = .terminate .success [] := by
  obtain ⟨final,run,ffi⟩ := nestedCall_hol_run
  rw [nestedCall_declared_semantics]
  have result := source_semantics_of_return nestedSourceState final (ofString "main") 4
    (.val (.word 7)) run
  simpa [ffi,sourceFfi] using result

/-- The HOL source run reaches five statement nodes across its two calls. -/
theorem nestedCall_controlSteps :
    controlSteps (.call none (ofString "main") []) {nestedSourceState with clock := 4} = 5 := by
  have leafMain : (ofString "leaf" == ofString "main") = false := by decide
  have middleMain : (ofString "middle" == ofString "main") = false := by decide
  have leafMiddle : (ofString "leaf" == ofString "middle") = false := by decide
  simp [controlSteps.eq_def,leafMain,middleMain,leafMiddle,evaluateHOLFiniteState_call,
    nestedSourceState,nestedCallEntry,progToHOL,expToHOL,shapeToHOL,sourceTemplate,
    evalListHOLFinite,evalListHOLExact,PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,
    HolFiniteMapExact.lookup_update,FUPDATE,
    evaluateHOLFiniteState_return,callEntryStateHOLFinite,evalHOLExact,shapeOfHOLExact,shapeEqHOL,
    setVarHOLFinite,emptyLocalsHOLFinite,fixClockHOLFinite]
  simp only [show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (3,a) (4,b) from
      by intro _ _; apply Prod.Lex.left; omega,
    show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (2,a) (3,b) from
      by intro _ _; apply Prod.Lex.left; omega,
    show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (1,a) (2,b) from
      by intro _ _; apply Prod.Lex.left; omega,
    show ∀ a b, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) (1,a) (3,b) from
      by intro _ _; apply Prod.Lex.left; omega, if_true]

/-- The entry with its ordinary call belongs to the call-aware frontend. -/
theorem nestedCall_frontend (ctxt : PanToCrepContextExact 64) : CallFrontend ctxt (progToHOL nestedCallEntry) := by
  simp only [nestedCallEntry,progToHOL,expToHOL,shapeToHOL]
  apply CallFrontend.decCall
  · simp
  · apply CallFrontend.base
    apply FrontendProgram.ret
    apply FrontendScalar.local (ofString "answer") (ctxt.vmax+1)
    simp [decCallSlots,HolFiniteMapExact.lookup_update,FUPDATE]

/-- The remaining functions provide the tail-call and return cases. -/
theorem nestedCall_callees_frontend (ctxt : PanToCrepContextExact 64) :
    CallFrontend ctxt (.call none (ofString "leaf") []) ∧
    CallFrontend ctxt (.return (.const 7)) := by
  exact ⟨.tail (by simp), .base (.ret (.const 7))⟩

/-- Every actual witness function has call-aware frontend syntax. -/
theorem nestedCall_frontendCode (ctxt : PanToCrepContextExact 64) : CallFrontendCode ctxt nestedSourceState.code := by
  intro name params body rsh found
  simp only [nestedSourceState,sourceTemplate,HolFiniteMapExact.lookup_update,FUPDATE] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    exact (nestedCall_callees_frontend _).2
  · split at found
    · simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨rfl,rfl,rfl⟩ := found
      exact (nestedCall_callees_frontend _).1
    · split at found
      · simp only [Option.some.injEq,Prod.mk.injEq] at found
        obtain ⟨rfl,rfl,rfl⟩ := found
        exact nestedCall_frontend _
      · simp at found

end SteppedFlapjack.Concrete
