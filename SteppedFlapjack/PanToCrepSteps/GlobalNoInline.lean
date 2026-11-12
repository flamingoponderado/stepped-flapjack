import SteppedFlapjack.PanToCrepSteps.GlobalCrepEntry
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-- Global lowering preserves declarations without inline-marked functions. -/
theorem compileDecs_noInline {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (h : declarations.filter inlinableHOL = []) (ctxt : PanGlobalsContextExact width) :
    (compileDecsExactHOL ctxt declarations).2.1.filter inlinableHOL = [] ∧
      (compileDecsExactHOL ctxt declarations).2.2.1.filter inlinableHOL = [] := by
  induction declarations generalizing ctxt with
  | nil => simp [compileDecsExactHOL]
  | cons d ds ih =>
    have ht : ds.filter inlinableHOL = [] := by
      by_cases hd : inlinableHOL d = true
      · simp [hd] at h
      · simpa [List.filter_cons,hd] using h
    cases d with
    | name name fields => simpa [compileDecsExactHOL] using ih ht ctxt
    | exnDecl name shape => simpa [compileDecsExactHOL,inlinableHOL] using ih ht ctxt
    | decl shape name value => simpa [compileDecsExactHOL] using ih ht _
    | function fn =>
      have hn : fn.inline = false := by
        cases hi : fn.inline <;> simp [inlinableHOL,hi] at h ⊢
      simpa [compileDecsExactHOL,inlinableHOL,hn] using ih ht ctxt


/-- Function renaming preserves the inline flags. -/
theorem fperm_noInline {width : Nat} [NeZero width] (f g : MlString)
    (declarations : List (DeclHOL width)) (h : declarations.filter inlinableHOL = []) :
    (fpermDecsHOL f g declarations).filter inlinableHOL = [] := by
  induction declarations with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih =>
    have ht : ds.filter inlinableHOL = [] := by
      by_cases hd : inlinableHOL d = true
      · simp [hd] at h
      · simpa [List.filter_cons,hd] using h
    cases d with
    | function fn =>
      have hn : fn.inline = false := by
        cases hi : fn.inline <;> simp [inlinableHOL,hi] at h ⊢
      simpa [fpermDecsHOL,inlinableHOL,hn] using ih ht
    | decl shape name value => simpa [fpermDecsHOL,inlinableHOL] using ih ht
    | exnDecl name shape => simpa [fpermDecsHOL,inlinableHOL] using ih ht
    | name name fields => simpa [fpermDecsHOL,inlinableHOL] using ih ht

/-- Declaration reordering preserves the inline flags. -/
theorem resort_noInline {width : Nat} [NeZero width] (declarations : List (DeclHOL width))
    (h : declarations.filter inlinableHOL = []) : (resortDeclsHOL declarations).filter inlinableHOL = [] := by
  induction declarations with
  | nil => simp [resortDeclsHOL]
  | cons d ds ih =>
    have ht : ds.filter inlinableHOL = [] := by
      by_cases hd : inlinableHOL d = true
      · simp [hd] at h
      · simpa [List.filter_cons,hd] using h
    cases d with
    | function fn =>
      have hn : fn.inline = false := by
        cases hi : fn.inline <;> simp [inlinableHOL,hi] at h ⊢
      simpa [resortDeclsHOL,isNameHOL,isExnDeclHOL,isDeclHOL,isFunctionHOL,inlinableHOL,hn] using ih ht
    | decl shape name value => simpa [resortDeclsHOL,isNameHOL,isExnDeclHOL,isDeclHOL,isFunctionHOL,inlinableHOL] using ih ht
    | exnDecl name shape => simpa [resortDeclsHOL,isNameHOL,isExnDeclHOL,isDeclHOL,isFunctionHOL,inlinableHOL] using ih ht
    | name name fields => simpa [resortDeclsHOL,isNameHOL,isExnDeclHOL,isDeclHOL,isFunctionHOL,inlinableHOL] using ih ht


/-- The generated entry and lowered declarations retain absent inline flags. -/
theorem compileTop_noInline {width : Nat} [NeZero width] (declarations : List (DeclHOL width))
    (h : declarations.filter inlinableHOL = []) (start : MlString) :
    (compileTopExactHOL declarations start).filter inlinableHOL = [] := by
  have hrenamed := fperm_noInline start (newMainNameHOL declarations) (resortDeclsHOL declarations) (resort_noInline declarations h)
  unfold compileTopExactHOL
  split
  · rfl
  · rename_i arguments body shape found
    let renamed := fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)
    let initial : PanGlobalsContextExact width :=
      {globals := HolFiniteMapExact.empty, globalsSize := 0,
       maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum}
    have no := compileDecs_noInline renamed hrenamed initial
    change (let (is,fs,es,_) := compileDecsExactHOL initial renamed
      let params := arguments.map (fun (entry : MlString × ShapeHOL) => ExpHOL.var .local entry.1)
      let main : DeclHOL width := .function ⟨start,false,false,arguments,.seq (nestedSeqHOL is) (.call none (newMainNameHOL declarations) params),shape⟩
      es ++ main :: fs).filter inlinableHOL = []
    simp only [List.filter_append,List.filter_cons,inlinableHOL]
    simp [no.1,no.2]

end SteppedFlapjack.PanToCrepSteps
