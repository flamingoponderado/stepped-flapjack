import SteppedFlapjack.CrepToLoopSteps.Branch
import SteppedFlapjack.LoopToWordSteps.WordSimpLoop
import SteppedFlapjack.LoopSteps.BranchedStatic
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.LoopToWordSteps

/-- Scalar expressions built from direct expressions and nested arithmetic,
shifts and comparisons. -/
inductive CompiledScalar {width : Nat} [NeZero width] : CrepExpHOL width → Prop
  | direct {e} : DirectExpression e → CompiledScalar e
  | load {address} : CompiledScalar address → CompiledScalar (.load address)
  | op (operator) {a b} : CompiledScalar a → CompiledScalar b → CompiledScalar (.op operator [a,b])
  | shift (operator) {a b} : CompiledScalar a → CompiledScalar b → CompiledScalar (.shift operator a b)
  | cmp (operator) {a b} : CompiledScalar a → CompiledScalar b → CompiledScalar (.cmp operator a b)

def PrefixShape {width : Nat} [NeZero width] (code : List (HolLoopProg width)) : Prop :=
  (∀ p ∈ code, BranchedProgram p) ∧ (∀ p ∈ code, LoopSelectProgram p) ∧
    (∀ p ∈ code, LoopBranch p)

theorem PrefixShape.append {width : Nat} [NeZero width] {a b : List (HolLoopProg width)}
    (ha : PrefixShape a) (hb : PrefixShape b) : PrefixShape (a ++ b) := by
  refine ⟨?_,?_,?_⟩ <;> intro p member <;> simp only [List.mem_append] at member
  · exact member.elim (ha.1 p) (hb.1 p)
  · exact member.elim (ha.2.1 p) (hb.2.1 p)
  · exact member.elim (ha.2.2 p) (hb.2.2 p)

theorem compiledScalar_prefix {width : Nat} [NeZero width] {e : CrepExpHOL width}
    (shape : CompiledScalar e) : ∀ (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet),
    ∃ code value next outLive, compileExpHOLExact ctxt tmp live e = (code,value,next,outLive) ∧ PrefixShape code := by
  induction shape with
  | direct direct =>
    intro ctxt tmp live
    obtain ⟨value,compiled⟩ := directExpression_noCode direct ctxt tmp live
    exact ⟨[],value,tmp,live,compiled,by simp [PrefixShape]⟩
  | load address ih =>
    intro ctxt tmp live
    obtain ⟨code,value,next,outLive,compiled,prefixShape⟩ := ih ctxt tmp live
    exact ⟨code,.load value,next,outLive,by simp [compileExpHOLExact,compiled],prefixShape⟩
  | @shift operator a b ha hb iha ihb =>
    intro ctxt tmp live
    obtain ⟨ca,va,na,la,ea,pa⟩ := iha ctxt tmp live
    obtain ⟨cb,vb,nb,lb,eb,pb⟩ := ihb ctxt na la
    refine ⟨ca ++ cb,.shift operator va vb,nb,lb,?_,pa.append pb⟩
    simp only [compileExpHOLExact,ea,eb]
  | @op operator a b ha hb iha ihb =>
    intro ctxt tmp live
    obtain ⟨ca,va,na,la,ea,pa⟩ := iha ctxt tmp live
    obtain ⟨cb,vb,nb,lb,eb,pb⟩ := ihb ctxt na la
    refine ⟨ca ++ cb,.op operator [va,vb],nb,lb,?_,pa.append pb⟩
    simp only [compileExpHOLExact,compileExpsHOLExact,ea,eb,List.append_nil]
  | @cmp operator a b ha hb iha ihb =>
    intro ctxt tmp live
    obtain ⟨ca,va,na,la,ea,pa⟩ := iha ctxt tmp live
    obtain ⟨cb,vb,nb,lb,eb,pb⟩ := ihb ctxt na la
    let suffix : List (HolLoopProg width) := [.assign (nb+1) va, .assign (nb+2) vb,
      .ite operator (nb+1) (.reg (nb+2)) (.assign (nb+1) (.const 1))
        (.assign (nb+1) (.const 0)) (sptListInsert [nb+1,nb+2] lb)]
    have ps : PrefixShape suffix := by
      refine ⟨?_,?_,?_⟩ <;> intro p hp
      · simp only [suffix,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact .leaf (.assign _ _)
        · exact .leaf (.assign _ _)
        · exact .ite _ _ _ _ (.leaf (.assign _ _)) (.leaf (.assign _ _))
      · simp only [suffix,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact .assign _ _
        · exact .assign _ _
        · exact .ite _ _ _ _ (.assign _ _) (.assign _ _)
      · simp only [suffix,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact .assign _ _
        · exact .assign _ _
        · exact .ite _ _ _ _ (.assign _ _) (.assign _ _)
    refine ⟨ca ++ cb ++ suffix,.var (nb+1),nb+3,sptListInsert [nb+1,nb+2] lb,?_,(pa.append pb).append ps⟩
    simp only [compileExpHOLExact,ea,eb,progIfHOLExact,suffix]


/-- A list of scalar arguments compiles to loop-free prefixes, preserving
argument order and the length of the value list. -/
theorem compiledScalars_prefix {width : Nat} [NeZero width]
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∃ code values next outLive,
      compileExpsHOLExact ctxt tmp live args = (code,values,next,outLive) ∧
      values.length = args.length ∧ PrefixShape code := by
  induction args generalizing tmp live with
  | nil => exact ⟨[],[],tmp,live,by simp [compileExpsHOLExact],rfl,by simp [PrefixShape]⟩
  | cons e es ih =>
    obtain ⟨code,value,next,outLive,compiled,headShape⟩ :=
      compiledScalar_prefix (shape e (by simp)) ctxt tmp live
    obtain ⟨rest,values,final,finalLive,compiledRest,len,restShape⟩ :=
      ih (by intro x hx; exact shape x (by simp [hx])) next outLive
    refine ⟨code ++ rest,value :: values,final,finalLive,?_,by simp [len],headShape.append restShape⟩
    simp only [compileExpsHOLExact,compiled,compiledRest]


/-- Scalar expression costs are stable across compiler contexts and live sets. -/
private def prefixMass {width : Nat} [NeZero width] (code : List (HolLoopProg width)) : Nat :=
  (code.map (fun p => 1 + LoopSteps.structuralWeight p)).sum

private theorem prefixMass_append {width : Nat} [NeZero width] (a b : List (HolLoopProg width)) :
    prefixMass (a ++ b) = prefixMass a + prefixMass b := by simp [prefixMass]

private theorem prefixMass_scalar {width : Nat} [NeZero width] {e : CrepExpHOL width}
    (shape : CompiledScalar e) : ∀ c d : CrepToLoopContextExact, ∀ t u : Nat, ∀ l m : NumSet,
      prefixMass (compileExpHOLExact c t l e).1 = prefixMass (compileExpHOLExact d u m e).1 := by
  induction shape with
  | direct h =>
    intro c d t u l m
    obtain ⟨v,hv⟩ := directExpression_noCode h c t l
    obtain ⟨w,hw⟩ := directExpression_noCode h d u m
    simp [hv,hw]
  | load address ih =>
    intro c d t u l m
    simpa only [compileExpHOLExact] using ih c d t u l m
  | @shift op a b ha hb ia ib =>
    intro c d t u l m
    have x := ia c d t u l m
    have y := ib c d (compileExpHOLExact c t l a).2.2.1 (compileExpHOLExact d u m a).2.2.1
      (compileExpHOLExact c t l a).2.2.2 (compileExpHOLExact d u m a).2.2.2
    simp only [compileExpHOLExact]
    simp_all [prefixMass_append]
  | @op op a b ha hb ia ib =>
    intro c d t u l m
    have x := ia c d t u l m
    have y := ib c d (compileExpHOLExact c t l a).2.2.1 (compileExpHOLExact d u m a).2.2.1
      (compileExpHOLExact c t l a).2.2.2 (compileExpHOLExact d u m a).2.2.2
    simp only [compileExpHOLExact,compileExpsHOLExact]
    simp_all [prefixMass]
  | @cmp op a b ha hb ia ib =>
    intro c d t u l m
    have x := ia c d t u l m
    have y := ib c d (compileExpHOLExact c t l a).2.2.1 (compileExpHOLExact d u m a).2.2.1
      (compileExpHOLExact c t l a).2.2.2 (compileExpHOLExact d u m a).2.2.2
    simp only [compileExpHOLExact]
    simp_all [prefixMass,progIfHOLExact,LoopSteps.structuralWeight]
private theorem prefixMass_scalars {width : Nat} [NeZero width] (args : List (CrepExpHOL width))
    (shape : ∀ e ∈ args, CompiledScalar e) :
    ∀ c d : CrepToLoopContextExact, ∀ t u : Nat, ∀ l m : NumSet,
      prefixMass (compileExpsHOLExact c t l args).1 = prefixMass (compileExpsHOLExact d u m args).1 := by
  induction args with
  | nil => simp [compileExpsHOLExact,prefixMass]
  | cons e es ih =>
    intro c d t u l m
    have head := prefixMass_scalar (shape e (by simp)) c d t u l m
    have tail := ih (by intro x hx; exact shape x (by simp [hx])) c d
      (compileExpHOLExact c t l e).2.2.1 (compileExpHOLExact d u m e).2.2.1
      (compileExpHOLExact c t l e).2.2.2 (compileExpHOLExact d u m e).2.2.2
    simp only [compileExpsHOLExact]
    simp_all [prefixMass_append]

private theorem nestedPrefixWeight {width : Nat} [NeZero width] (code : List (HolLoopProg width)) :
    LoopSteps.structuralWeight (loopNestedSeqHOL code) = 1 + prefixMass code := by
  induction code with
  | nil => rfl
  | cons p ps ih => simp [loopNestedSeqHOL, LoopSteps.structuralWeight, prefixMass, ih]; omega

/-- A concrete argument list has the same prefix cost in every compiler context. -/
theorem scalarArgumentWeight {width : Nat} [NeZero width] (args : List (CrepExpHOL width))
    (shape : ∀ e ∈ args, CompiledScalar e) (c d : CrepToLoopContextExact) (t u : Nat) (l m : NumSet) :
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpsHOLExact c t l args).1) =
      LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpsHOLExact d u m args).1) := by
  simp only [nestedPrefixWeight, prefixMass_scalars args shape c d t u l m]
/-- A scalar expression has the same prefix cost in every compiler context. -/
theorem scalarExpressionWeight {width : Nat} [NeZero width] {e : CrepExpHOL width}
    (shape : CompiledScalar e) (c d : CrepToLoopContextExact) (t u : Nat) (l m : NumSet) :
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact c t l e).1) =
      LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact d u m e).1) := by
  simp only [nestedPrefixWeight, prefixMass_scalar shape c d t u l m]

end SteppedFlapjack.CrepToLoopSteps
