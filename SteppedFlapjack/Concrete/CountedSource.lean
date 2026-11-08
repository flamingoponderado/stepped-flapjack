import SteppedFlapjack.Concrete.CountedShape
import Flapjack.Pancake.Semantics.PanSem.TotalEvalRanged
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps Flapjack.Basis.Pure.MlString

/-- Result relation for the call-free scalar source fragment. -/
inductive CountedOutcome {σ : Type} (initial : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanValueFfiControlResult (RiscV.Word 64) σ → Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 σ → Prop
  | normal (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock} final.toExact)
      (ranged : PanSemStateRelExecRanged {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock})
      (words : WordLocals locals) : CountedOutcome initial (.normal locals globals memory ffi) none final
  | returned (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (word : BitVec 64) (final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock} final.toExact)
      (ranged : PanSemStateRelExecRanged {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock})
      (words : WordLocals locals) : CountedOutcome initial (.returned locals globals memory ffi [.word word])
        (some (.returned (.val (.word word)))) final

  | error (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
      (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock} final.toExact)
      (ranged : PanSemStateRelExecRanged {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := final.clock})
      (words : WordLocals locals) : CountedOutcome initial (.error locals globals memory ffi) (some .error) final

/-- Runtime fields may be threaded between statements without changing the
persistent source machine context carried by the result relation. -/
private theorem outcomeRebase {σ : Type}
    (initial : PanSemState (RiscV.Word 64) (FfiState σ))
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (ffi : FfiState σ) (clock : Nat)
    {result : PanValueFfiControlResult (RiscV.Word 64) σ} {hol : Option (PanSemResultExact 64)}
    {final : PanSemStateFiniteExact 64 σ}
    (outcome : CountedOutcome {initial with locals := locals, globals := globals, memory := memory, ffi := ffi, clock := clock}
      result hol final) : CountedOutcome initial result hol final := by
  cases outcome with
  | normal l g m f final rel ranged words =>
    exact .normal l g m f final (by simpa using rel) (by simpa using ranged) words
  | returned l g m f word final rel ranged words =>
    exact .returned l g m f word final (by simpa using rel) (by simpa using ranged) words
  | error l g m f final rel ranged words =>
    exact .error l g m f final (by simpa using rel) (by simpa using ranged) words

def CountedNonError {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Prop
  | .error _ _ _ _ => False
  | _ => True

/-- A failed expression costs zero counted steps but still visits its statement. -/
def countedErrorBonus {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Nat
  | .error _ _ _ _ => 1
  | _ => 0

private def Bridge (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs],
    PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production → WordLocals production.locals →
    ProgByteRanged program → ∀ (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
      (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
      (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
      (result : PanValueFfiControlResult (RiscV.Word 64) σ),
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count) →
      count ≤ source.clock →
      ∃ holResult sourceFinal,
        source.evaluateHOLFiniteState (progToHOL program) = (holResult,sourceFinal) ∧
        CountedOutcome production result holResult sourceFinal ∧
        controlSteps (progToHOL program) source ≤ count + countedErrorBonus result ∧ source.clock ≤ sourceFinal.clock + count

private theorem errorLeaf {σ : Type} (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (program : Prog (RiscV.Word 64)) (count : Nat)
    (hol : source.evaluateHOLFiniteState (progToHOL program) = (some .error,source))
    (visits : controlSteps (progToHOL program) source = 1) :
    ∃ holResult sourceFinal,
      source.evaluateHOLFiniteState (progToHOL program) = (holResult,sourceFinal) ∧
      CountedOutcome production (.error production.locals production.globals production.memory production.ffi) holResult sourceFinal ∧
      controlSteps (progToHOL program) source ≤ count + countedErrorBonus (.error production.locals production.globals production.memory production.ffi) ∧
      source.clock ≤ sourceFinal.clock + count := by
  have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
  refine ⟨some .error,source,hol,?_,?_,by omega⟩
  · apply CountedOutcome.error
    · simpa [clockEq] using rel
    · simpa [clockEq] using ranged
    · exact words
  · simp [visits,countedErrorBonus]

private theorem skipBridge : Bridge .skip := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps,Option.some.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
    refine ⟨none,source,?_,?_,?_,?_⟩
    · simp only [progToHOL,evaluateHOLFiniteState_skip]
    · apply CountedOutcome.normal
      · simpa [clockEq] using rel
      · simpa [clockEq] using ranged
      · exact words
    · simp [progToHOL,controlSteps.eq_def]
    · omega
private theorem returnBridge {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) : Bridge (.return expression) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    have originalRun := run
    simp only [evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none =>
      simp only [evaluated,Option.map_none,Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      have exprRanged : ExpByteRanged expression := by simpa [ProgByteRanged] using byteRanged
      obtain ⟨_,hol,visits⟩ := counted_scalar_return_error production source rel ranged words expression scalar exprRanged
        context primitive handler functions (fuel+1) 0 originalRun
      exact errorLeaf production source rel ranged words (.return expression) 0 (by simpa [progToHOL] using hol)
        (by simpa [progToHOL] using visits)
    | some value =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some value := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
        have exprRanged : ExpByteRanged expression := by simpa [ProgByteRanged] using byteRanged
        have inverted := counted_return_invert production source rel ranged expression exprRanged word
          context primitive handler functions (fuel+1) (panValueExpStepCost expression+1) originalRun
        obtain ⟨hol,finalRel,finalRanged,bound⟩ := inverted
        have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
        refine ⟨some (.returned (.val (.word word))),source.emptyLocalsHOLFinite,?_,?_,?_,?_⟩
        · simpa [progToHOL] using hol
        · apply CountedOutcome.returned
          · simpa [emptyLocalsHOLFinite,panEmptyLocals,clockEq] using finalRel
          · simpa [emptyLocalsHOLFinite,panEmptyLocals,clockEq] using finalRanged
          · exact wordLocals_empty
        · simpa [progToHOL,countedErrorBonus] using bound
        · simp [emptyLocalsHOLFinite]
      · have expressionRun : evalPanSemStateExp production expression = some value := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
        rename_i invalid
        simp at invalid

private theorem assignBridge {scope : List VarName} (name : VarName) {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) : Bridge (.assign .local name expression) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget
  have nameRanged : NameRanged name := by simpa [ProgByteRanged] using byteRanged.1
  have exprRanged : ExpByteRanged expression := by simpa [ProgByteRanged] using byteRanged.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    have originalRun := run
    simp only [evalPanValueFfiProgSteps,panValueAssignLocalSteps,evalPanValueExpCountedWith,evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none =>
      simp only [evaluated,Option.map_none,Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      obtain ⟨hol,visits⟩ := counted_assign_error production source rel ranged name nameRanged expression exprRanged
        context primitive handler functions (fuel+1) 0 originalRun
      exact errorLeaf production source rel ranged words (.assign .local name expression) 0 (by simpa [progToHOL] using hol)
        (by simpa [progToHOL] using visits)
    | some value =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some value := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words value expressionRun
        obtain ⟨assigned,postEq,hol,finalRel,finalRanged,bound⟩ :=
          counted_assign_invert production source rel ranged name nameRanged expression exprRanged
            context primitive handler functions (fuel+1) (panValueExpStepCost expression+1)
            (updatePanValueMap production.locals name (.word word)) originalRun
        have valueEq : assigned = .word word := by
          have h := congrFun postEq name
          simpa [updatePanValueMap] using h.symm
        subst assigned
        let final := setVarHOLFinite (ofString name) (.val (.word word)) source
        have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
        refine ⟨none,final,?_,?_,?_,?_⟩
        · simpa [progToHOL,panValueToHOL,final] using hol
        · apply CountedOutcome.normal
          · simpa [final,setVarHOLFinite,clockEq] using finalRel
          · simpa [final,setVarHOLFinite,clockEq] using finalRanged
          · exact wordLocals_update words name word
        · simpa [progToHOL,final,countedErrorBonus] using bound
        · simp [final,setVarHOLFinite]
      · simp only [Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨hol,visits⟩ := counted_assign_error production source rel ranged name nameRanged expression exprRanged
          context primitive handler functions (fuel+1) (panValueExpStepCost expression+1) originalRun
        exact errorLeaf production source rel ranged words (.assign .local name expression) (panValueExpStepCost expression+1)
          (by simpa [progToHOL] using hol) (by simpa [progToHOL] using visits)

private theorem iteBridge {scope : List VarName} {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (aBound : Bridge a) (bBound : Bridge b) : Bridge (.ite condition a b) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget
  have condRanged : ExpByteRanged condition := by simpa [ProgByteRanged] using byteRanged.1
  have aRanged : ProgByteRanged a := by simpa [ProgByteRanged] using byteRanged.2.1
  have bRanged : ProgByteRanged b := by simpa [ProgByteRanged] using byteRanged.2.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps] at run
    cases condRun : panValueIteCondition production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
        production.locals production.globals production.memory condition (some (panSemBitVec64MemoryAccess production)) with
    | none =>
      simp [condRun] at run
      obtain ⟨rfl,rfl⟩ := run
      have condExact := counted_scalar_condition_error production source rel ranged words condition scalar condRanged condRun
      apply errorLeaf production source rel ranged words (.ite condition a b) 0
      · simp only [progToHOL]
        rw [evaluateHOLFiniteState_ite,condExact]
      · simp only [progToHOL]
        rw [controlSteps_ite,condExact]
        rfl
    | some pair =>
      rcases pair with ⟨word,condCost⟩
      have condExact := (counted_condition_invert production source rel ranged condition condRanged word condCost condRun).1
      by_cases zero : word = 0
      · cases branchRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
            production.locals production.globals production.memory production.ffi b
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
        | none => simp [condRun,zero,branchRun] at run
        | some branch =>
          rcases branch with ⟨branchResult,branchCost⟩
          simp [condRun,zero,branchRun] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨holResult,sourceFinal,hol,outcome,bound,clock⟩ := bBound production source rel ranged words bRanged
            context primitive handler functions fuel branchCost branchResult branchRun (by omega)
          refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
          · simp only [progToHOL]
            rw [evaluateHOLFiniteState_ite,condExact]
            simpa [zero] using hol
          · simp only [progToHOL]
            rw [controlSteps_ite,condExact]
            simp only [zero,ne_eq,not_true_eq_false,if_false]
            omega
      · have zeroBits : word ≠ (0#64) := by simpa using zero
        cases branchRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
            production.locals production.globals production.memory production.ffi a
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
        | none => simp [condRun,zeroBits,branchRun] at run
        | some branch =>
          rcases branch with ⟨branchResult,branchCost⟩
          simp [condRun,zeroBits,branchRun] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨holResult,sourceFinal,hol,outcome,bound,clock⟩ := aBound production source rel ranged words aRanged
            context primitive handler functions fuel branchCost branchResult branchRun (by omega)
          refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
          · simp only [progToHOL]
            rw [evaluateHOLFiniteState_ite,condExact]
            simpa [zeroBits] using hol
          · simp only [progToHOL]
            rw [controlSteps_ite,condExact]
            simp only [if_pos zero]
            omega

private theorem seqBridge {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (aShape : SupportedIn scope a) (aBound : Bridge a) (bBound : Bridge b) : Bridge (.seq a b) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget
  have aRanged : ProgByteRanged a := by simpa [ProgByteRanged] using byteRanged.1
  have bRanged : ProgByteRanged b := by simpa [ProgByteRanged] using byteRanged.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps] at run
    cases firstRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi a
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => simp [firstRun] at run
    | some first =>
      rcases first with ⟨firstResult,firstCost⟩
      have basic := supported_counted_basic context primitive handler production.structs functions
        production.baseAddress production.topAddress (some (panSemBitVec64MemoryAccess production)) fuel aShape
        _ _ _ _ firstResult firstCost firstRun
      cases firstResult with
      | normal nextLocals nextGlobals nextMemory nextFfi =>
        cases secondRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
            nextLocals nextGlobals nextMemory nextFfi b
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
        | none => simp [firstRun,secondRun] at run
        | some second =>
          rcases second with ⟨secondResult,secondCost⟩
          simp [firstRun,secondRun] at run
          obtain ⟨rfl,rfl⟩ := run
          obtain ⟨firstHol,sourceMiddle,holFirst,firstOutcome,firstBound,firstClock⟩ :=
            aBound production source rel ranged words aRanged context primitive handler functions fuel firstCost
              (.normal nextLocals nextGlobals nextMemory nextFfi) firstRun (by omega)
          simp only [countedErrorBonus,Nat.add_zero] at firstBound
          cases firstOutcome with
          | normal l g m f final nextRel nextRanged nextWords =>
            have memEq : sourceMiddle.memaddrs = source.memaddrs := by
              funext address
              apply propext
              exact (nextRel.2.2.2.2.2.2.1 address).symm.trans (rel.2.2.2.2.2.2.1 address)
            let _ : DecidablePred sourceMiddle.memaddrs := by rw [memEq]; exact dec
            let next := {production with locals := nextLocals, globals := nextGlobals, memory := nextMemory, ffi := nextFfi, clock := sourceMiddle.clock}
            have nextRun : evalPanValueFfiProgSteps context primitive handler next.structs functions
                next.baseAddress next.topAddress panSemBitVec64BytesInWord fuel
                next.locals next.globals next.memory next.ffi b (memoryAccess := some (panSemBitVec64MemoryAccess next)) =
                some (secondResult,secondCost) := by simpa [next,panSemBitVec64MemoryAccess] using secondRun
            obtain ⟨holResult,sourceFinal,holSecond,secondOutcome,secondBound,secondClock⟩ :=
              bBound next sourceMiddle nextRel nextRanged nextWords bRanged context primitive handler functions fuel secondCost
                secondResult nextRun (by omega)
            refine ⟨holResult,sourceFinal,?_,?_,?_,by omega⟩
            · simp only [progToHOL]
              rw [evaluateHOLFiniteState_seq_line780,holFirst]
              exact holSecond
            · exact outcomeRebase production nextLocals nextGlobals nextMemory nextFfi sourceMiddle.clock secondOutcome
            · simp only [progToHOL]
              rw [controlSteps_seq,holFirst]
              simp only
              omega
      | returned l g m f values =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨holResult,sourceFinal,holFirst,outcome,firstBound,firstClock⟩ :=
          aBound production source rel ranged words aRanged context primitive handler functions fuel firstCost
            (.returned l g m f values) firstRun (by omega)
        refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
        · simp only [progToHOL]
          rw [evaluateHOLFiniteState_seq_line780,holFirst]
          cases outcome; simp
        · simp only [progToHOL]
          rw [controlSteps_seq,holFirst]
          cases outcome; simp only; omega
      | error l g m f =>
        simp [firstRun] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨holResult,sourceFinal,holFirst,outcome,firstBound,firstClock⟩ :=
          aBound production source rel ranged words aRanged context primitive handler functions fuel firstCost
            (.error l g m f) firstRun (by omega)
        simp only [countedErrorBonus] at firstBound
        refine ⟨holResult,sourceFinal,?_,outcome,?_,by omega⟩
        · simp only [progToHOL]
          rw [evaluateHOLFiniteState_seq_line780,holFirst]
          cases outcome; simp
        · simp only [progToHOL]
          rw [controlSteps_seq,holFirst]
          cases outcome; simp only [countedErrorBonus]; omega
      | raised l g m f e v => exact False.elim basic
      | broke l g m f => exact False.elim basic
      | continued l g m f => exact False.elim basic
      | finalFfi l g m f e => exact False.elim basic

private theorem restoreOutcome {σ : Type}
    (initial : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ)
    (rel : PanSemStateRelExec initial source.toExact) (ranged : PanSemStateRelExecRanged initial)
    (words : WordLocals initial.locals) (name : VarName) (nameRanged : NameRanged name)
    (word : BitVec 64) {result : PanValueFfiControlResult (RiscV.Word 64) σ}
    {hol : Option (PanSemResultExact 64)} {final : PanSemStateFiniteExact 64 σ}
    (outcome : CountedOutcome {initial with locals := updatePanValueMap initial.locals name (.word word)} result hol final) :
    CountedOutcome initial (restorePanValueFfiLocal name (initial.locals name) result) hol
      {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))} := by
  have saved := rel.1 name nameRanged
  have restoreEq (current : VarName → Option (PanValue (RiscV.Word 64))) :
      restorePanValueLocal current name (initial.locals name) = resVar current (name,initial.locals name) := by
    funext key
    by_cases same : key = name
    · subst key; cases initial.locals name <;> simp [restorePanValueLocal,resVar,FDOMSUB,FUPDATE]
    · have reverse : name ≠ key := Ne.symm same
      cases initial.locals name <;> simp [restorePanValueLocal,resVar,FDOMSUB,FUPDATE,same,reverse]
  cases outcome with
  | normal l g m f final nextRel nextRanged nextWords =>
    simp only [restorePanValueFfiLocal]
    apply CountedOutcome.normal
    · have h := nextRel.resVarLocals name nameRanged (initial.locals name)
      simpa [restoreEq, saved] using h
    · have h := PanSemStateRelExecRanged.resVarLocals nextRanged name (initial.locals name) (ranged.1 name)
      simpa [restoreEq] using h
    · exact wordLocals_restore nextWords words name
  | returned l g m f value final nextRel nextRanged nextWords =>
    simp only [restorePanValueFfiLocal]
    apply CountedOutcome.returned
    · have h := nextRel.resVarLocals name nameRanged (initial.locals name)
      simpa [restoreEq, saved] using h
    · have h := PanSemStateRelExecRanged.resVarLocals nextRanged name (initial.locals name) (ranged.1 name)
      simpa [restoreEq] using h
    · exact wordLocals_restore nextWords words name
  | error l g m f final nextRel nextRanged nextWords =>
    simp only [restorePanValueFfiLocal]
    apply CountedOutcome.error
    · have h := nextRel.resVarLocals name nameRanged (initial.locals name)
      simpa [restoreEq, saved] using h
    · have h := PanSemStateRelExecRanged.resVarLocals nextRanged name (initial.locals name) (ranged.1 name)
      simpa [restoreEq] using h
    · exact wordLocals_restore nextWords words name

private theorem declBridge {scope : List VarName} (name : VarName) {initializer : Exp (RiscV.Word 64)}
    {body : Prog (RiscV.Word 64)} (scalar : Scalar scope initializer) (bodyBound : Bridge body) :
    Bridge (.dec name .one initializer body) := by
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget
  have nameRanged : NameRanged name := by simpa [ProgByteRanged] using byteRanged.1
  have initRanged : ExpByteRanged initializer := by simpa [ProgByteRanged] using byteRanged.2.2.1
  have bodyRanged : ProgByteRanged body := by simpa [ProgByteRanged] using byteRanged.2.2.2
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    simp only [evalPanValueFfiProgSteps] at run
    cases initRun : panValueDecAccepted production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
        production.locals production.globals production.memory initializer (some (panSemBitVec64MemoryAccess production)) .one with
    | none =>
      simp [initRun] at run
      obtain ⟨rfl,rfl⟩ := run
      have initExact := counted_scalar_initializer_error production source rel ranged words initializer scalar initRanged initRun
      apply errorLeaf production source rel ranged words (.dec name .one initializer body) 0
      · simp only [progToHOL,shapeToHOL]
        rw [evaluateHOLFiniteState_dec_total]
        simp only [initExact]
      · simp only [progToHOL,shapeToHOL]
        rw [controlSteps.eq_def]
        simp [initExact]
    | some pair =>
      rcases pair with ⟨value,initCost⟩
      obtain ⟨word,rfl,costEq,initHol⟩ := counted_scalar_initializer_invert production source rel ranged words initializer
        scalar initRanged value initCost initRun
      subst initCost
      let entry := {production with locals := updatePanValueMap production.locals name (.word word)}
      let sourceEntry := setVarHOLFinite (ofString name) (.val (.word word)) source
      have entryRel : PanSemStateRelExec entry sourceEntry.toExact := by
        simpa [entry,sourceEntry,panValueToHOL] using rel.updateLocals name nameRanged (.word word)
      have entryRanged : PanSemStateRelExecRanged entry := by
        exact PanSemStateRelExecRanged.updateLocals ranged name (.word word) (by simp [PanValueByteRanged])
      have entryWords : WordLocals entry.locals := wordLocals_update words name word
      let _ : DecidablePred sourceEntry.memaddrs := dec
      cases bodyRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
          (updatePanValueMap production.locals name (.word word)) production.globals production.memory production.ffi body
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
      | none => simp [initRun,bodyRun] at run
      | some pair =>
        rcases pair with ⟨bodyResult,bodyCost⟩
        simp [initRun,bodyRun] at run
        obtain ⟨rfl,rfl⟩ := run
        have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
            entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
            (memoryAccess := some (panSemBitVec64MemoryAccess entry)) = some (bodyResult,bodyCost) := by
          simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
        obtain ⟨holResult,bodyFinal,hol,outcome,bound,clock⟩ := bodyBound entry sourceEntry entryRel entryRanged entryWords bodyRanged
          context primitive handler functions fuel bodyCost bodyResult entryRun (by simp [sourceEntry,setVarHOLFinite]; omega)
        have valid : shapeEqHOL .one (shapeOfHOLExact (.val (.word word))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
        have bonusEq : countedErrorBonus (restorePanValueFfiLocal name (production.locals name) bodyResult) = countedErrorBonus bodyResult := by
          cases bodyResult <;> rfl
        refine ⟨holResult,{bodyFinal with locals := HolFiniteMapExact.resVarEq bodyFinal.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_,?_⟩
        · simp only [progToHOL,shapeToHOL]
          rw [evaluateHOLFiniteState_dec_total]
          simp only [initHol,valid,if_true]
          rw [show (setVarHOLFinite (ofString name) (.val (.word word)) source).evaluateHOLFiniteState (progToHOL body) = (holResult,bodyFinal) from hol]
        · exact restoreOutcome production source rel ranged words name nameRanged word outcome
        · simp only [progToHOL,shapeToHOL]
          rw [controlSteps_dec _ _ _ _ _ _ initHol valid,bonusEq]
          simp only [sourceEntry] at bound
          omega
        · simp [sourceEntry,setVarHOLFinite] at clock
          simp only
          omega

private theorem whileBridge {scope : List VarName} {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (bodyShape : SupportedIn scope body) (bodyBound : Bridge body) : Bridge (.while condition body) := by
  have loopAt : ∀ fuel {σ : Type} (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs],
      PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production → WordLocals production.locals →
      ProgByteRanged (.while condition body) → ∀ (context : PanValueFfiContext (RiscV.Word 64))
      (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
      (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (count : Nat)
      (result : PanValueFfiControlResult (RiscV.Word 64) σ),
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi (.while condition body)
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count) →
      count ≤ source.clock →
      ∃ holResult sourceFinal, source.evaluateHOLFiniteState (progToHOL (.while condition body)) = (holResult,sourceFinal) ∧
        CountedOutcome production result holResult sourceFinal ∧
        controlSteps (progToHOL (.while condition body)) source ≤ count + countedErrorBonus result ∧ source.clock ≤ sourceFinal.clock + count := by
    intro fuel
    induction fuel with
    | zero =>
      intro σ production source dec rel ranged words byteRanged context primitive handler functions count result run
      simp [evalPanValueFfiProgSteps] at run
    | succ fuel ih =>
      intro σ production source dec rel ranged words byteRanged context primitive handler functions count result run budget
      have condRanged : ExpByteRanged condition := by simpa [ProgByteRanged] using byteRanged.1
      have bodyRanged : ProgByteRanged body := by simpa [ProgByteRanged] using byteRanged.2
      simp only [evalPanValueFfiProgSteps] at run
      cases condRun : panValueIteCondition production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
          production.locals production.globals production.memory condition (some (panSemBitVec64MemoryAccess production)) with
      | none =>
        simp [condRun] at run
        obtain ⟨rfl,rfl⟩ := run
        have condExact := counted_scalar_condition_error production source rel ranged words condition scalar condRanged condRun
        have condFinite : @evalHOLFinite 64 σ _ source
            (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = none := condExact
        apply errorLeaf production source rel ranged words (.while condition body) 0
        · simp only [progToHOL]
          rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
        · simp only [progToHOL]
          rw [controlSteps_while,condExact]
          rfl
      | some pair =>
        rcases pair with ⟨word,condCost⟩
        obtain ⟨condExact,costEq⟩ := counted_condition_invert production source rel ranged condition condRanged word condCost condRun
        subst condCost
        have condFinite : @evalHOLFinite 64 σ _ source
            (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = some (.val (.word word)) := condExact
        by_cases zero : word = 0
        · simp [condRun,zero] at run
          obtain ⟨rfl,rfl⟩ := run
          have clockEq : source.clock = production.clock := rel.2.2.2.2.2.2.2.2.1
          refine ⟨none,source,?_,?_,?_,?_⟩
          · simp only [progToHOL]
            rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
            simp [zero]
          · apply CountedOutcome.normal
            · simpa [clockEq] using rel
            · simpa [clockEq] using ranged
            · exact words
          · simp only [progToHOL]
            rw [controlSteps_while]
            simp [condExact,zero,countedErrorBonus]
          · omega
        · have zeroBits : word ≠ (0#64) := by simpa using zero
          let _ : DecidablePred source.decClockHOLFinite.memaddrs := dec
          cases bodyRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
              production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
              production.locals production.globals production.memory production.ffi body
              (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
          | none => simp [condRun,zeroBits,bodyRun] at run
          | some pair =>
            rcases pair with ⟨bodyResult,bodyCost⟩
            have basic := supported_counted_basic context primitive handler production.structs functions production.baseAddress production.topAddress
              (some (panSemBitVec64MemoryAccess production)) fuel bodyShape _ _ _ _ bodyResult bodyCost bodyRun
            cases bodyResult with
            | normal l g m f =>
              cases restRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
                  production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel l g m f (.while condition body)
                  (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
              | none => simp [condRun,zeroBits,bodyRun,restRun] at run
              | some pair =>
                rcases pair with ⟨restResult,restCost⟩
                simp [condRun,zeroBits,bodyRun,restRun] at run
                obtain ⟨rfl,rfl⟩ := run
                have positive : source.clock ≠ 0 := by omega
                let entry := {production with clock := production.clock - 1}
                have entryRel : PanSemStateRelExec entry source.decClockHOLFinite.toExact := by
                  simpa [entry,decClockHOLFinite,decClockHOLExact] using rel.decClock
                have entryRanged : PanSemStateRelExecRanged entry := PanSemStateRelExecRanged.setClock ranged _
                have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
                    entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
                    (memoryAccess := some (panSemBitVec64MemoryAccess entry)) = some (.normal l g m f,bodyCost) := by
                  simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
                obtain ⟨_,middle,holBody,outcome,bodyVisit,bodyClock⟩ := bodyBound entry source.decClockHOLFinite entryRel entryRanged words bodyRanged
                  context primitive handler functions fuel bodyCost (.normal l g m f) entryRun (by simp [decClockHOLFinite]; omega)
                simp only [countedErrorBonus,Nat.add_zero] at bodyVisit
                cases outcome with
                | normal _ _ _ _ _ nextRel nextRanged nextWords =>
                  have memEq : middle.memaddrs = source.memaddrs := by
                    funext address
                    apply propext
                    exact (nextRel.2.2.2.2.2.2.1 address).symm.trans (rel.2.2.2.2.2.2.1 address)
                  let _ : DecidablePred middle.memaddrs := by rw [memEq]; exact dec
                  let next := {production with locals := l, globals := g, memory := m, ffi := f, clock := middle.clock}
                  have nextRun : evalPanValueFfiProgSteps context primitive handler next.structs functions next.baseAddress next.topAddress
                      panSemBitVec64BytesInWord fuel next.locals next.globals next.memory next.ffi (.while condition body)
                      (memoryAccess := some (panSemBitVec64MemoryAccess next)) = some (restResult,restCost) := by
                    simpa [next,panSemBitVec64MemoryAccess] using restRun
                  obtain ⟨holResult,final,holRest,restOutcome,restVisit,restClock⟩ := ih next middle nextRel nextRanged nextWords byteRanged
                    context primitive handler functions restCost restResult nextRun (by simp [decClockHOLFinite] at bodyClock; omega)
                  simp only [progToHOL] at holRest restVisit
                  refine ⟨holResult,final,?_,?_,?_,?_⟩
                  · simp only [progToHOL]
                    rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
                    simp [zeroBits,positive,holBody,holRest]
                  · exact outcomeRebase production l g m f middle.clock restOutcome
                  · simp only [progToHOL]
                    rw [controlSteps_while]
                    simp only [condExact,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨zero,positive⟩),holBody]
                    change 1 + (controlSteps (progToHOL body) source.decClockHOLFinite +
                      controlSteps (.while (expToHOL condition) (progToHOL body)) middle) ≤ _
                    omega
                  · simp [decClockHOLFinite] at bodyClock
                    omega
            | returned l g m f values =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have positive : source.clock ≠ 0 := by omega
              let entry := {production with clock := production.clock - 1}
              have entryRel : PanSemStateRelExec entry source.decClockHOLFinite.toExact := by
                simpa [entry,decClockHOLFinite,decClockHOLExact] using rel.decClock
              have entryRanged : PanSemStateRelExecRanged entry := PanSemStateRelExecRanged.setClock ranged _
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
                  entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry)) = some (.returned l g m f values,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨holResult,final,holBody,outcome,bodyVisit,bodyClock⟩ := bodyBound entry source.decClockHOLFinite entryRel entryRanged words bodyRanged
                context primitive handler functions fuel bodyCost (.returned l g m f values) entryRun (by simp [decClockHOLFinite]; omega)
              refine ⟨holResult,final,?_,?_,?_,?_⟩
              · simp only [progToHOL]
                rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
                cases outcome
                simp [zeroBits,positive,holBody]
              · exact outcomeRebase production production.locals production.globals production.memory production.ffi (production.clock-1) outcome
              · simp only [progToHOL]
                rw [controlSteps_while]
                simp only [condExact,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨zero,positive⟩),holBody]
                cases outcome
                simp only [Nat.add_zero]
                omega
              · simp [decClockHOLFinite] at bodyClock
                omega
            | error l g m f =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,rfl⟩ := run
              have positive : source.clock ≠ 0 := by omega
              let entry := {production with clock := production.clock - 1}
              have entryRel : PanSemStateRelExec entry source.decClockHOLFinite.toExact := by
                simpa [entry,decClockHOLFinite,decClockHOLExact] using rel.decClock
              have entryRanged : PanSemStateRelExecRanged entry := PanSemStateRelExecRanged.setClock ranged _
              have entryRun : evalPanValueFfiProgSteps context primitive handler entry.structs functions
                  entry.baseAddress entry.topAddress panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
                  (memoryAccess := some (panSemBitVec64MemoryAccess entry)) = some (.error l g m f,bodyCost) := by
                simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
              obtain ⟨holResult,final,holBody,outcome,bodyVisit,bodyClock⟩ := bodyBound entry source.decClockHOLFinite entryRel entryRanged words bodyRanged
                context primitive handler functions fuel bodyCost (.error l g m f) entryRun (by simp [decClockHOLFinite]; omega)
              simp only [countedErrorBonus] at bodyVisit
              refine ⟨holResult,final,?_,?_,?_,?_⟩
              · simp only [progToHOL]
                rw [evaluateHOLFiniteState_while_fixClockRewrite,condFinite]
                cases outcome
                simp [zeroBits,positive,holBody]
              · exact outcomeRebase production production.locals production.globals production.memory production.ffi (production.clock-1) outcome
              · simp only [progToHOL]
                rw [controlSteps_while]
                simp only [condExact,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨zero,positive⟩),holBody]
                cases outcome
                simp only [Nat.add_zero,countedErrorBonus]
                omega
              · simp [decClockHOLFinite] at bodyClock
                omega
            | raised l g m f e v => exact False.elim basic
            | broke l g m f => exact False.elim basic
            | continued l g m f => exact False.elim basic
            | finalFfi l g m f e => exact False.elim basic
  intro σ production source dec rel ranged words byteRanged context primitive handler functions fuel count result run budget
  exact loopAt fuel production source rel ranged words byteRanged context primitive handler functions count result run budget

private theorem supportedBridge {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : Bridge program := by
  induction supported with
  | skip => exact skipBridge
  | assign name member scalar => exact assignBridge name scalar
  | decl name scalar shape ih => exact declBridge name scalar ih
  | seq a b iha ihb => exact seqBridge a iha ihb
  | ite scalar a b iha ihb => exact iteBridge scalar iha ihb
  | «while» scalar body ih => exact whileBridge scalar body ih
  | ret scalar => exact returnBridge scalar

/-- A counted run of a supported body is a corresponding HOL run when the
source clock covers its explicitly given count. Clock consumption is bounded
by the count, and control visits by the count plus the error-result bonus. -/
theorem supported_counted_source {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs] (rel : PanSemStateRelExec production source.toExact)
    (ranged : PanSemStateRelExecRanged production) (words : WordLocals production.locals)
    (byteRanged : ProgByteRanged program) (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,count))
    (budget : count ≤ source.clock) :
    ∃ holResult sourceFinal, source.evaluateHOLFiniteState (progToHOL program) = (holResult,sourceFinal) ∧
      CountedOutcome production result holResult sourceFinal ∧
      controlSteps (progToHOL program) source ≤ count + countedErrorBonus result ∧ source.clock ≤ sourceFinal.clock + count :=
  supportedBridge supported production source rel ranged words byteRanged context primitive handler functions fuel count result run budget

end SteppedFlapjack.Concrete
