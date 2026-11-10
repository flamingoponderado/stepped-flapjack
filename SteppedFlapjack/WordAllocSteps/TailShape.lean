import SteppedFlapjack.WordAllocSteps.TailEntry

/-! Static preservation of direct-tail entry shapes through Word compilation. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.WordAlloc Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordSimp
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy
open Flapjack.Compiler.Backend.WordUnreach
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps
open SteppedFlapjack.WordDeadSteps SteppedFlapjack.WordCseSteps SteppedFlapjack.WordCopySteps
open SteppedFlapjack.WordTwoRegSteps SteppedFlapjack.WordUnreachSteps

/-- Every direct tail entry has unrestricted allowed destinations. -/
theorem tailEntry_allowed_all {width : Nat} [NeZero width] {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) : AllowedTailEntry (fun _ => True) p := by
  induction shape with
  | branch h => exact .branch h
  | call loc => exact .call loc trivial
  | seq _ _ a b => exact .seq a b

/-- The complete pre-allocation pass retains direct-tail structure, without
assuming an execution or a code-table relation. -/
theorem preAlloc_tailEntry_allowed {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (flag : Bool) (count : Nat)
    {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)} (shape : AllowedTailEntry allowed p) :
    AllowedTailEntry allowed (preAlloc ac flag count p) := by
  have h0 := compileExp_allowedTailEntry shape
  have h1 := select_allowedTailEntry ac (maxVarHOL (compileExp p)+1) h0
  have h2 := fullSsa_allowedTailEntry count h1
  have h3 := removeDead_allowedTailEntry h2 .ln [] []
  have h4 := wordCse_allowedTailEntry h3 emptyData
  have h5 := copy_allowedTailEntry h4 emptyEq
  have h6 : AllowedTailEntry allowed (threeToTwoRegProg flag
      (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans count
        (instSelect ac (maxVarHOL (compileExp p)+1) (compileExp p))))))) := by
    cases flag with
    | false => exact h5
    | true => exact threeToTwo_allowedTailEntry h5
  have h7 := seqAssocRight_allowedTailEntry h6 (.branch .skip)
  exact removeDead_allowedTailEntry h7 .ln [] []

/-- Full Word compilation preserves every allowed direct-call destination. -/
theorem fullCompileSingle_tailEntry_allowed {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (flag : Bool) (count fc alg k : Nat)
    (col : Option (Spt Nat)) {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) :
    RegAllowedTail allowed (fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2 := by
  have input := allowed_regTail (preAlloc_tailEntry_allowed ac flag count shape)
  have allocated := wordAlloc_regAllowed fc ac alg k col input
  change RegAllowedTail allowed (Flapjack.Compiler.Backend.WordRemove.removeMustTerminate
    (wordAlloc fc ac alg k (preAlloc ac flag count p) col))
  rw [removeMustTerminate_regTail (regAllowed_shape allocated)]
  exact allocated

/-- Full Word compilation keeps the direct-tail entry shape. -/
theorem fullCompileSingle_tailEntry_shape {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (flag : Bool) (count fc alg k : Nat)
    (col : Option (Spt Nat)) {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p) :
    RegTailShape (fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2 :=
  regAllowed_shape (fullCompileSingle_tailEntry_allowed ac flag count fc alg k col (tailEntry_allowed_all shape))

private theorem zip_left_member {α β : Type} (xs : List α) (ys : List β)
    (x : α) (y : β) (h : (x,y) ∈ xs.zip ys) : x ∈ xs := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [List.zip_cons_cons,List.mem_cons,Prod.mk.injEq] at h
      rcases h with ⟨rfl,_⟩ | h
      · simp
      · exact List.mem_cons_of_mem _ (ih ys h)

/-- If all input functions are direct-tail entries or loop sequences, the
whole Word compiler produces only bitmap-free allocated bodies. -/
theorem wholeCompile_tailOrLoop_shape {width : Nat} [NeZero width]
    (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (shapes : ∀ row ∈ programs, WordTailEntryShape row.2.2 ∨ LoopSequence row.2.2) :
    ∀ row ∈ (compile wc ac programs).2,
      RegTailShape row.2.2 ∨ LoopSequence row.2.2 ∨ SteppedFlapjack.WordToStackSteps.LoopBlock row.2.2 := by
  intro row member
  change row ∈ ((programs.zip (nextNOracle programs.length wc.colOracle).1).map
    (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac)) at member
  obtain ⟨⟨⟨name,count,p⟩,col⟩,hin,rfl⟩ := List.mem_map.mp member
  have source := shapes (name,count,p) (zip_left_member programs _ _ _ hin)
  rcases source with tail | loop
  · exact Or.inl (fullCompileSingle_tailEntry_shape ac ac.twoRegArith count name wc.regAlg
      (ac.regCount-(5+ac.avoidRegs.length)) col tail)
  · exact Or.inr (Or.inr (fullCompileSingle_stackReady ac ac.twoRegArith count name wc.regAlg
      (ac.regCount-(5+ac.avoidRegs.length)) col loop).1)

end SteppedFlapjack.WordAllocSteps
