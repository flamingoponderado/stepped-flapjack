import SteppedFlapjack.PanToCrepSteps.CountedWhile

/-! Finite loop traces for counted and HOL source correspondence. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Evidence for a finite loop run. Each iteration contains actual body
executions and the proved bound for that body; the loop exits on zero, break,
return, or a final FFI event. -/
inductive CountedWhileTrace {σ : Type}
    (condition : Exp (RiscV.Word 64)) (body : Prog (RiscV.Word 64)) (bodyHOL : ProgHOL 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    Nat → PanSemState (RiscV.Word 64) (FfiState σ) → PanSemStateFiniteExact 64 σ →
      PanValueFfiControlResult (RiscV.Word 64) σ → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 σ → Nat → Prop where
  | zero (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
      (conditionRanged : ExpByteRanged condition)
      (conditionRun : evalPanSemStateExp production condition = some (.word 0)) :
      CountedWhileTrace condition body bodyHOL context primitive handler functions (fuel+1) production source
        (.normal production.locals production.globals production.memory production.ffi) none source (panValueExpStepCost condition+1)
  | breakExit (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
      (conditionRanged : ExpByteRanged condition) (word : BitVec 64)
      (conditionRun : evalPanSemStateExp production condition = some (.word word))
      (nonzero : word ≠ 0) (clock : source.clock ≠ 0)
      (localsPost globalsPost : VarName → Option (PanValue (RiscV.Word 64)))
      (memoryPost : BitVec 64 → Option (PanValue (BitVec 64))) (ffiPost : FfiState σ) (bodyCost : Nat)
      (bodyExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi body
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.broke localsPost globalsPost memoryPost ffiPost,bodyCost))
      (bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState bodyHOL = (some .break,final))
      (bodyBound : controlSteps bodyHOL source.decClockHOLFinite ≤ bodyCost) :
      CountedWhileTrace condition body bodyHOL context primitive handler functions (fuel+1) production source
        (.normal localsPost globalsPost memoryPost ffiPost) none final (panValueExpStepCost condition+bodyCost+1)
  | terminalExit (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
      (conditionRanged : ExpByteRanged condition) (word : BitVec 64)
      (conditionRun : evalPanSemStateExp production condition = some (.word word))
      (nonzero : word ≠ 0) (clock : source.clock ≠ 0)
      (localsPost globalsPost : VarName → Option (PanValue (RiscV.Word 64)))
      (memoryPost : BitVec 64 → Option (PanValue (BitVec 64))) (ffiPost : FfiState σ) (bodyCost : Nat)
      (terminal : Sum (BitVec 64) (FfiFinalEvent × HolFinalEvent))
      (terminalRel : match terminal with | .inl _ => True | .inr events => FfiFinalEventRel events.1 events.2)
      (bodyExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi body
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (match terminal with
            | .inl value => .returned localsPost globalsPost memoryPost ffiPost [.word value]
            | .inr events => .finalFfi localsPost globalsPost memoryPost ffiPost events.1,bodyCost))
      (bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState bodyHOL =
        (some (match terminal with | .inl value => .returned (.val (.word value)) | .inr events => .finalFfi events.2),final))
      (bodyBound : controlSteps bodyHOL source.decClockHOLFinite ≤ bodyCost) :
      CountedWhileTrace condition body bodyHOL context primitive handler functions (fuel+1) production source
        (match terminal with
          | .inl value => .returned localsPost globalsPost memoryPost ffiPost [.word value]
          | .inr events => .finalFfi localsPost globalsPost memoryPost ffiPost events.1)
        (some (match terminal with | .inl value => .returned (.val (.word value)) | .inr events => .finalFfi events.2))
        final (panValueExpStepCost condition+bodyCost+1)
  | iteration (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source middle final : PanSemStateFiniteExact 64 σ)
      (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
      (conditionRanged : ExpByteRanged condition) (word : BitVec 64)
      (conditionRun : evalPanSemStateExp production condition = some (.word word))
      (nonzero : word ≠ 0) (clock : source.clock ≠ 0)
      (localsPost globalsPost : VarName → Option (PanValue (RiscV.Word 64)))
      (memoryPost : BitVec 64 → Option (PanValue (BitVec 64))) (ffiPost : FfiState σ)
      (continued : Bool) (bodyCost restCost : Nat)
      (result : PanValueFfiControlResult (RiscV.Word 64) σ) (holResult : Option (PanSemResultExact 64))
      (bodyExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi body
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some ((if continued then .continued localsPost globalsPost memoryPost ffiPost
          else .normal localsPost globalsPost memoryPost ffiPost),bodyCost))
      (bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState bodyHOL =
        (if continued then some .continue else none,middle))
      (bodyBound : controlSteps bodyHOL source.decClockHOLFinite ≤ bodyCost)
      (rest : CountedWhileTrace condition body bodyHOL context primitive handler functions fuel
        {production with locals := localsPost, globals := globalsPost, memory := memoryPost, ffi := ffiPost, clock := middle.clock}
        middle result holResult final restCost) :
      CountedWhileTrace condition body bodyHOL context primitive handler functions (fuel+1) production source
        result holResult final (panValueExpStepCost condition+bodyCost+restCost+1)

/-- Any finite traced loop yields the actual counted and HOL runs, and its
HOL control visits are bounded by the actual counted source cost. -/
theorem counted_while_trace {σ : Type}
    (condition : Exp (RiscV.Word 64)) (body : Prog (RiscV.Word 64)) (bodyHOL : ProgHOL 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    {fuel : Nat} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {source final : PanSemStateFiniteExact 64 σ} {result : PanValueFfiControlResult (RiscV.Word 64) σ}
    {holResult : Option (PanSemResultExact 64)} {cost : Nat}
    (trace : CountedWhileTrace condition body bodyHOL context primitive handler functions fuel production source result holResult final cost) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.while condition body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,cost) ∧
    source.evaluateHOLFiniteState (.while (expToHOL condition) bodyHOL) = (holResult,final) ∧
    controlSteps (.while (expToHOL condition) bodyHOL) source ≤ cost := by
  classical
  induction trace with
  | zero fuel production source rel ranged conditionRanged conditionRun =>
    exact counted_while_zero production source rel ranged condition conditionRanged conditionRun
      context primitive handler functions fuel body bodyHOL
  | breakExit fuel production source final rel ranged conditionRanged word conditionRun nonzero clock
      localsPost globalsPost memoryPost ffiPost bodyCost bodyExec bodyRun bodyBound =>
    exact counted_while_break production source final rel ranged condition conditionRanged word conditionRun nonzero clock
      context primitive handler functions fuel body bodyHOL localsPost globalsPost memoryPost ffiPost bodyCost bodyExec bodyRun bodyBound
  | terminalExit fuel production source final rel ranged conditionRanged word conditionRun nonzero clock
      localsPost globalsPost memoryPost ffiPost bodyCost terminal terminalRel bodyExec bodyRun bodyBound =>
    cases terminal with
    | inl value =>
      obtain ⟨exec,run,bound,_⟩ := counted_while_terminal production source final rel ranged condition conditionRanged word
        conditionRun nonzero clock context primitive handler functions fuel body bodyHOL localsPost globalsPost memoryPost ffiPost
        bodyCost (.inl value) terminalRel bodyExec bodyRun bodyBound
      exact ⟨exec,run,bound⟩
    | inr events =>
      obtain ⟨exec,run,bound,_⟩ := counted_while_terminal production source final rel ranged condition conditionRanged word
        conditionRun nonzero clock context primitive handler functions fuel body bodyHOL localsPost globalsPost memoryPost ffiPost
        bodyCost (.inr events) terminalRel bodyExec bodyRun bodyBound
      exact ⟨exec,run,bound⟩
  | iteration fuel production source middle final rel ranged conditionRanged word conditionRun nonzero clock
      localsPost globalsPost memoryPost ffiPost continued bodyCost restCost result holResult bodyExec bodyRun bodyBound rest ih =>
    have restExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        localsPost globalsPost memoryPost ffiPost (.while condition body)
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,restCost) := by
      simpa [panSemBitVec64MemoryAccess] using ih.1
    exact counted_while_iteration production source middle final rel ranged condition conditionRanged word conditionRun
      nonzero clock context primitive handler functions fuel body bodyHOL localsPost globalsPost memoryPost ffiPost continued
      bodyCost restCost result holResult bodyExec bodyRun bodyBound restExec ih.2.1 ih.2.2

end SteppedFlapjack.PanToCrepSteps
