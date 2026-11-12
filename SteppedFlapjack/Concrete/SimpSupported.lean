import SteppedFlapjack.Concrete.Fragment
import Flapjack.Pancake.PanSimp
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang

private theorem smartSupported {scope : List VarName} {pre next : Prog (RiscV.Word 64)}
    (hpre : SupportedIn scope pre) (hnext : SupportedIn scope next) : SupportedIn scope (smartSeq pre next) := by
  cases pre <;> simp_all [smartSeq,SupportedIn.seq]

private theorem assocSupported {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ∀ pre, SupportedIn scope pre → SupportedIn scope (seqAssoc pre program) := by
  induction supported with
  | skip => intro pre hpre; simpa [seqAssoc] using hpre
  | store address value => intro pre hpre; simpa only [seqAssoc] using smartSupported hpre (.store address value)
  | assign name member scalar => intro pre hpre; simpa only [seqAssoc] using smartSupported hpre (.assign name member scalar)
  | ret scalar => intro pre hpre; simpa only [seqAssoc] using smartSupported hpre (.ret scalar)
  | decl name scalar body ih =>
    intro pre hpre
    simpa only [seqAssoc] using smartSupported hpre (.decl name scalar (ih .skip .skip))
  | seq a b iha ihb =>
    intro pre hpre
    simpa only [seqAssoc] using ihb _ (iha _ hpre)
  | ite scalar a b iha ihb =>
    intro pre hpre
    simpa only [seqAssoc] using smartSupported hpre (.ite scalar (iha .skip .skip) (ihb .skip .skip))
  | «while» scalar body ih =>
    intro pre hpre
    simpa only [seqAssoc] using smartSupported hpre (.while scalar (ih .skip .skip))

private theorem retSupportedIdentity {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : retToTail program = program := by
  induction supported with
  | skip | store | assign | ret => simp [retToTail]
  | decl name scalar body ih => simp [retToTail,ih]
  | seq a b iha ihb =>
    simp only [retToTail,iha,ihb]
    cases a <;> simp_all [seqCallRet]
  | ite scalar a b iha ihb => simp [retToTail,iha,ihb]
  | «while» scalar body ih => simp [retToTail,ih]

private theorem smartRanged (pre next : Prog (RiscV.Word 64))
    (hpre : ProgByteRanged pre) (hnext : ProgByteRanged next) : ProgByteRanged (smartSeq pre next) := by
  cases pre <;> simp only [smartSeq,ProgByteRanged] at * <;> aesop

private theorem assocRanged {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ProgByteRanged program →
      ∀ pre, ProgByteRanged pre → ProgByteRanged (seqAssoc pre program) := by
  induction supported with
  | skip => intro _ pre hpre; simpa [seqAssoc] using hpre
  | store address value => intro ranged pre hpre; simpa only [seqAssoc] using smartRanged pre _ hpre ranged
  | assign name member scalar => intro ranged pre hpre; simpa only [seqAssoc] using smartRanged pre _ hpre ranged
  | ret scalar => intro ranged pre hpre; simpa only [seqAssoc] using smartRanged pre _ hpre ranged
  | decl name scalar body ih =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    rw [seqAssoc]
    apply smartRanged pre _ hpre
    simpa only [ProgByteRanged] using ⟨ranged.1,ranged.2.1,ranged.2.2.1,ih ranged.2.2.2 .skip (by simp [ProgByteRanged])⟩
  | seq a b iha ihb =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    simpa only [seqAssoc] using ihb ranged.2 _ (iha ranged.1 pre hpre)
  | ite scalar a b iha ihb =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    rw [seqAssoc]
    apply smartRanged pre _ hpre
    simpa only [ProgByteRanged] using ⟨ranged.1,iha ranged.2.1 .skip (by simp [ProgByteRanged]),
      ihb ranged.2.2 .skip (by simp [ProgByteRanged])⟩
  | «while» scalar body ih =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    rw [seqAssoc]
    apply smartRanged pre _ hpre
    simpa only [ProgByteRanged] using ⟨ranged.1,ih ranged.2 .skip (by simp [ProgByteRanged])⟩

private theorem smartHOL (pre next : Prog (RiscV.Word 64)) :
    progToHOL (smartSeq pre next) = smartSeqHOL (progToHOL pre) (progToHOL next) := by
  cases pre <;> simp [smartSeq,smartSeqHOL,progToHOL]
  case call info name args =>
    cases info with
    | none => simp [progToHOL]
    | some pair =>
      rcases pair with ⟨returns,handler⟩
      cases handler with
      | none => simp [progToHOL]
      | some triple =>
        rcases triple with ⟨eid,var,body⟩
        simp [progToHOL]

private theorem assocHOL {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ∀ pre, progToHOL (seqAssoc pre program) =
      seqAssocHOL (progToHOL pre) (progToHOL program) := by
  induction supported with
  | skip => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL]
  | store | assign | ret => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,smartHOL]
  | decl name scalar body ih => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,shapeToHOL,smartHOL,ih]
  | seq a b iha ihb => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,iha,ihb]
  | ite scalar a b iha ihb => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,smartHOL,iha,ihb]
  | «while» scalar body ih => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,smartHOL,ih]

private theorem retHOLIdentity {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : retToTailHOL (progToHOL program) = progToHOL program := by
  induction supported with
  | skip | store | assign | ret => simp [progToHOL,retToTailHOL]
  | decl name scalar body ih => simp [progToHOL,retToTailHOL,ih]
  | seq a b iha ihb =>
    simp only [progToHOL,retToTailHOL,iha,ihb]
    cases a <;> simp_all [progToHOL,seqCallRetHOL]
  | ite scalar a b iha ihb => simp [progToHOL,retToTailHOL,iha,ihb]
  | «while» scalar body ih => simp [progToHOL,retToTailHOL,ih]

/-- Simplification of a supported program remains supported, and its HOL
output agrees exactly with simplifying the representable source program. -/
theorem supported_panSimp (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    CallFreeSupported (panSimpProg program) ∧
      panSimpCompileHOL (progToHOL program) = progToHOL (panSimpProg program) := by
  have shape := assocSupported supported.1 .skip .skip
  have ranged := assocRanged supported.1 supported.2 .skip (by simp [ProgByteRanged])
  have identity := retSupportedIdentity shape
  constructor
  · simpa [panSimpProg,identity] using (show CallFreeSupported (seqAssoc .skip program) from ⟨shape,ranged⟩)
  · have converted := assocHOL supported.1 .skip
    simp only [progToHOL] at converted
    rw [panSimpCompileHOL,← converted,retHOLIdentity shape,panSimpProg,identity]

/-- On supported programs, reassociation already is the full simplifier. -/
theorem supported_seqAssocHOL (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    seqAssocHOL .skip (progToHOL program) = progToHOL (panSimpProg program) := by
  have shape := assocSupported supported.1 .skip .skip
  have identity := retSupportedIdentity shape
  have converted := assocHOL supported.1 .skip
  simp only [progToHOL] at converted
  simpa [panSimpProg,identity] using converted.symm

/-- Reassociation preserves the fragment with ordinary and tail calls. -/
private theorem smartCallSupported {scope : List VarName} {pre next : Prog (RiscV.Word 64)}
    (hpre : CallSupportedIn scope pre) (hnext : CallSupportedIn scope next) :
    CallSupportedIn scope (smartSeq pre next) := by
  cases pre <;> simp_all [smartSeq,CallSupportedIn.seq]

private theorem assocBaseCallSupported {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) :
    ∀ pre, CallSupportedIn scope pre → CallSupportedIn scope (seqAssoc pre program) := by
  induction supported with
  | skip => intro pre hpre; simpa [seqAssoc] using hpre
  | store address value => intro pre hpre; simpa only [seqAssoc] using smartCallSupported hpre (.base (.store address value))
  | assign name member scalar => intro pre hpre; simpa only [seqAssoc] using smartCallSupported hpre (.base (.assign name member scalar))
  | ret scalar => intro pre hpre; simpa only [seqAssoc] using smartCallSupported hpre (.base (.ret scalar))
  | decl name scalar body ih =>
    intro pre hpre
    simpa only [seqAssoc] using smartCallSupported hpre (.decl name scalar (ih .skip (.base .skip)))
  | seq a b iha ihb => intro pre hpre; simpa only [seqAssoc] using ihb _ (iha _ hpre)
  | ite scalar a b iha ihb =>
    intro pre hpre
    simpa only [seqAssoc] using smartCallSupported hpre (.ite scalar (iha .skip (.base .skip)) (ihb .skip (.base .skip)))
  | «while» scalar body ih =>
    intro pre hpre
    simpa only [seqAssoc] using smartCallSupported hpre (.while scalar (ih .skip (.base .skip)))

private theorem assocCallSupported {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) :
    ∀ pre, CallSupportedIn scope pre → CallSupportedIn scope (seqAssoc pre program) := by
  induction supported with
  | base supported => exact assocBaseCallSupported supported
  | tail name args scalar => intro pre hpre; simpa only [seqAssoc] using smartCallSupported hpre (.tail name args scalar)
  | call dest name args scalar cont ih =>
    intro pre hpre
    simpa only [seqAssoc] using smartCallSupported hpre (.call dest name args scalar (ih .skip (.base .skip)))
  | decl name scalar body ih =>
    intro pre hpre
    simpa only [seqAssoc] using smartCallSupported hpre (.decl name scalar (ih .skip (.base .skip)))
  | seq a b iha ihb => intro pre hpre; simpa only [seqAssoc] using ihb _ (iha _ hpre)
  | ite scalar a b iha ihb =>
    intro pre hpre
    simpa only [seqAssoc] using smartCallSupported hpre (.ite scalar (iha .skip (.base .skip)) (ihb .skip (.base .skip)))
  | «while» scalar body ih =>
    intro pre hpre
    simpa only [seqAssoc] using smartCallSupported hpre (.while scalar (ih .skip (.base .skip)))

private theorem seqCallRet_callSupported {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope a) : seqCallRet (.seq a b) = .seq a b := by
  cases supported with
  | base h => cases h <;> simp [seqCallRet]
  | tail => simp [seqCallRet]
  | call => simp [seqCallRet]
  | decl => simp [seqCallRet]
  | seq => simp [seqCallRet]
  | ite => simp [seqCallRet]
  | «while» => simp [seqCallRet]

private theorem retCallSupportedIdentity {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : retToTail program = program := by
  induction supported with
  | base h => exact retSupportedIdentity h
  | tail => simp [retToTail]
  | call dest name args scalar cont ih => simp [retToTail,ih]
  | decl name scalar body ih => simp [retToTail,ih]
  | seq a b iha ihb => simp only [retToTail,iha,ihb]; exact seqCallRet_callSupported a
  | ite scalar a b iha ihb => simp [retToTail,iha,ihb]
  | «while» scalar body ih => simp [retToTail,ih]

/-- The source simplifier retains the supported call fragment. -/
theorem callSupported_panSimp {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : CallSupportedIn scope (panSimpProg program) := by
  have shape := assocCallSupported supported .skip (.base .skip)
  simpa [panSimpProg,retCallSupportedIdentity shape] using shape

private theorem assocCallHOL {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : ∀ pre, progToHOL (seqAssoc pre program) =
      seqAssocHOL (progToHOL pre) (progToHOL program) := by
  induction supported with
  | base h => exact assocHOL h
  | tail name args scalar => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,smartHOL]
  | call dest name args scalar cont ih =>
    intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,shapeToHOL,smartHOL,ih]
  | decl name scalar body ih => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,shapeToHOL,smartHOL,ih]
  | seq a b iha ihb => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,iha,ihb]
  | ite scalar a b iha ihb => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,smartHOL,iha,ihb]
  | «while» scalar body ih => intro pre; simp [seqAssoc,seqAssocHOL,progToHOL,smartHOL,ih]

private theorem seqCallRetHOL_callSupported {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope a) :
    seqCallRetHOL (.seq (progToHOL a) (progToHOL b)) = .seq (progToHOL a) (progToHOL b) := by
  cases supported with
  | base h => cases h <;> simp [progToHOL,seqCallRetHOL]
  | tail => simp [progToHOL,seqCallRetHOL]
  | call => simp [progToHOL,seqCallRetHOL]
  | decl => simp [progToHOL,seqCallRetHOL]
  | seq => simp [progToHOL,seqCallRetHOL]
  | ite => simp [progToHOL,seqCallRetHOL]
  | «while» => simp [progToHOL,seqCallRetHOL]

private theorem retCallHOLIdentity {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : retToTailHOL (progToHOL program) = progToHOL program := by
  induction supported with
  | base h => exact retHOLIdentity h
  | tail => simp [progToHOL,retToTailHOL]
  | call dest name args scalar cont ih => simp [progToHOL,retToTailHOL,ih]
  | decl name scalar body ih => simp [progToHOL,retToTailHOL,ih]
  | seq a b iha ihb => simp only [progToHOL,retToTailHOL,iha,ihb]; exact seqCallRetHOL_callSupported a
  | ite scalar a b iha ihb => simp [progToHOL,retToTailHOL,iha,ihb]
  | «while» scalar body ih => simp [progToHOL,retToTailHOL,ih]

/-- The HOL simplifier and executable simplifier agree for call-aware bodies. -/
theorem callSupported_panSimp_hol {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) :
    panSimpCompileHOL (progToHOL program) = progToHOL (panSimpProg program) := by
  have shape := assocCallSupported supported .skip (.base .skip)
  have converted := assocCallHOL supported .skip
  simp only [progToHOL] at converted
  rw [panSimpCompileHOL,← converted,retCallHOLIdentity shape,panSimpProg,retCallSupportedIdentity shape]

private theorem assocCallRanged {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : ProgByteRanged program →
      ∀ pre, ProgByteRanged pre → ProgByteRanged (seqAssoc pre program) := by
  induction supported with
  | base h => exact assocRanged h
  | tail name args scalar =>
    intro ranged pre hpre
    simpa only [seqAssoc] using smartRanged pre _ hpre ranged
  | call dest name args scalar cont ih =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    rw [seqAssoc]
    apply smartRanged pre _ hpre
    simpa only [ProgByteRanged] using ⟨ranged.1,ranged.2.1,ranged.2.2.1,ranged.2.2.2.1,
      ih ranged.2.2.2.2 .skip (by simp [ProgByteRanged])⟩
  | decl name scalar body ih =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    rw [seqAssoc]
    apply smartRanged pre _ hpre
    simpa only [ProgByteRanged] using ⟨ranged.1,ranged.2.1,ranged.2.2.1,ih ranged.2.2.2 .skip (by simp [ProgByteRanged])⟩
  | seq a b iha ihb =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    simpa only [seqAssoc] using ihb ranged.2 _ (iha ranged.1 pre hpre)
  | ite scalar a b iha ihb =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    rw [seqAssoc]
    apply smartRanged pre _ hpre
    simpa only [ProgByteRanged] using ⟨ranged.1,iha ranged.2.1 .skip (by simp [ProgByteRanged]),
      ihb ranged.2.2 .skip (by simp [ProgByteRanged])⟩
  | «while» scalar body ih =>
    intro ranged pre hpre
    simp only [ProgByteRanged] at ranged
    rw [seqAssoc]
    apply smartRanged pre _ hpre
    simpa only [ProgByteRanged] using ⟨ranged.1,ih ranged.2 .skip (by simp [ProgByteRanged])⟩

/-- Simplification preserves the byte-range requirement used by the source bridge. -/
theorem callSupported_panSimp_ranged {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) (ranged : ProgByteRanged program) :
    ProgByteRanged (panSimpProg program) := by
  have shape := assocCallSupported supported .skip (.base .skip)
  have range := assocCallRanged supported ranged .skip (by simp [ProgByteRanged])
  simpa [panSimpProg,retCallSupportedIdentity shape] using range

/-- On the call-aware fragment, simplification consists of reassociation. -/
theorem callSupported_seqAssocHOL {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) :
    seqAssocHOL .skip (progToHOL program) = progToHOL (panSimpProg program) := by
  have shape := assocCallSupported supported .skip (.base .skip)
  have converted := assocCallHOL supported .skip
  simp only [progToHOL] at converted
  simpa [panSimpProg,retCallSupportedIdentity shape] using converted.symm

end SteppedFlapjack.Concrete
