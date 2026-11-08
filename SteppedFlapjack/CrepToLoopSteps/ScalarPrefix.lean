import SteppedFlapjack.CrepToLoopSteps.BranchExtraClock
import SteppedFlapjack.LoopToWordSteps.WordSimpLoop
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.LoopToWordSteps

/-- Scalar expressions built from direct expressions and nested arithmetic,
shifts and comparisons. -/
inductive CompiledScalar {width : Nat} [NeZero width] : CrepExpHOL width → Prop
  | direct {e} : DirectExpression e → CompiledScalar e
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


end SteppedFlapjack.CrepToLoopSteps
