import SteppedFlapjack.CrepToLoopSteps.InlineFixed

/-! The non-inlined global-entry path through the actual Crep inliner. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.CrepInlineCanonical Flapjack.Pancake.PanLang
variable {width : Nat} [NeZero width]

/-- A call-free initializer followed by a tail call is fixed by inlining
whenever the callee is absent from the current inline map. -/
theorem inline_tailEntry_fixed
    (inl : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (keys : List CrepInlineMapHOLName) (support : ∀ k, inl.lookup k ≠ none → k ∈ keys)
    (init : CrepProgHOL width) (shape : BranchProgram init)
    (callee : CrepInlineMapHOLName) (args : List (CrepExpHOL width))
    (notInline : inl.lookup callee = none) :
    inlineProgHOLCoreExact inl keys support (.seq init (.call none callee args)) =
      .seq init (.call none callee args) := by
  rw [inlineProgHOLCoreExact_seq,branchProgram_inline_fixed inl keys support shape]
  rw [inlineProgHOLCoreExact_call_none]
  split <;> simp_all

/-- If the callee is not requested for inlining, the actual top-level inliner
preserves a generated call-free-initializer/tail-call entry at its index. -/
theorem compileInlTop_tailEntry_at
    (names : List CrepInlineMapHOLName)
    (code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (index : Nat) (hi : index < code.length) (entryName callee : CrepInlineMapHOLName)
    (init : CrepProgHOL width) (shape : BranchProgram init) (args : List (CrepExpHOL width))
    (entry : code[index] = (entryName,[],.seq init (.call none callee args)))
    (notInline : callee ∉ names) :
    ∃ h : index < (compileInlTopHOLExact names code).length,
      (compileInlTopHOLExact names code)[index]'h = (entryName,[],.seq init (.call none callee args)) := by
  unfold compileInlTopHOLExact compileInlProgHOLExactWithSupport
  refine ⟨by simpa using hi,?_⟩
  simp only [List.getElem_map,entry]
  apply congrArg (fun p => (entryName,[],p))
  apply inline_tailEntry_fixed _ _ _ init shape callee args
  by_contra h
  have hmem := HolFiniteMapExact.erase_support _ _ (supportKeys_alistToFmapHOLExact _) entryName callee h
  simp only [List.mem_filter,List.mem_map] at hmem
  obtain ⟨⟨candidate,hcandidate,hkey⟩,_⟩ := hmem
  have hname : callee ∈ names := by
    have : candidate.1 ∈ names := List.contains_iff_mem.mp hcandidate.2
    simpa only [hkey] using this
  exact notInline hname

/-- The whole Pancake-to-Crep pass preserves the generated tail-entry syntax
and therefore its precise Crep visit count when its target is not inline-marked. -/
theorem compileProgDecls_tailEntry_at {σ : Type}
    (declarations : List (DeclHOL width))
    (index : Nat) (hi : index < (compileToCrepExactHOLW declarations).length)
    (entryName callee : CrepInlineMapHOLName)
    (init : CrepProgHOL width) (shape : BranchProgram init) (args : List (CrepExpHOL width))
    (entry : (compileToCrepExactHOLW declarations)[index] = (entryName,[],.seq init (.call none callee args)))
    (notInline : callee ∉ (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst)
    (state : CrepSemHOLState width σ) :
    ∃ h : index < (compileProgDeclsHOLW declarations).length,
      (compileProgDeclsHOLW declarations)[index]'h = (entryName,[],.seq init (.call none callee args)) ∧
      CrepSteps.steps ((compileProgDeclsHOLW declarations)[index]'h).2.2 state =
        CrepSteps.steps (.seq init (.call none callee args)) state := by
  obtain ⟨h,eq⟩ := compileInlTop_tailEntry_at
    ((functionsHOL (declarations.filter inlinableHOL)).map Prod.fst) (compileToCrepExactHOLW declarations)
    index hi entryName callee init shape args entry notInline
  have h' : index < (compileProgDeclsHOLW declarations).length := by
    simpa only [compileProgDeclsHOLW] using h
  have eq' : (compileProgDeclsHOLW declarations)[index]'h' = (entryName,[],.seq init (.call none callee args)) := by
    simpa only [compileProgDeclsHOLW] using eq
  exact ⟨h',eq',by rw [eq']⟩

/-- When the generated Crep initializer and tail call succeed, the preserved
entry visits are exactly the sequence and call nodes plus reached executions. -/
theorem compileProgDecls_tailEntry_steps {σ : Type}
    (declarations : List (DeclHOL width))
    (index : Nat) (hi : index < (compileToCrepExactHOLW declarations).length)
    (entryName callee : CrepInlineMapHOLName)
    (init : CrepProgHOL width) (shape : BranchProgram init) (args : List (CrepExpHOL width))
    (entry : (compileToCrepExactHOLW declarations)[index] = (entryName,[],.seq init (.call none callee args)))
    (notInline : callee ∉ (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst)
    (state post : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (parameters : List Nat) (body : CrepProgHOL width)
    (initRun : evalCrepSemHOLProgExact state init = (none,post))
    (arguments : args.mapM (evalCrepSemHOLExp post) = some values)
    (found : post.code.lookup callee = some (parameters,body))
    (arity : parameters.length = values.length) (distinct : parameters.Nodup) (clock : post.clock ≠ 0) :
    ∃ h : index < (compileProgDeclsHOLW declarations).length,
      CrepSteps.steps ((compileProgDeclsHOLW declarations)[index]'h).2.2 state =
        2 + CrepSteps.steps init state + CrepSteps.steps body
          (decClockCrepSemHOL {post with locals := HolFiniteMapExact.empty.updateList (parameters.zip values)}) := by
  obtain ⟨h,_,stepsEq⟩ := compileProgDecls_tailEntry_at declarations index hi entryName callee init shape args entry notInline state
  refine ⟨h,?_⟩
  rw [stepsEq,CrepSteps.steps_seq,initRun]
  simp only
  rw [CrepSteps.steps_call_tail callee args post values parameters body arguments found arity distinct clock]
  omega

end SteppedFlapjack.CrepToLoopSteps
