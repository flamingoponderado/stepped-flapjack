module

public import Flapjack.PanValueFfiClockSemantics

@[expose] public section

/-!
# Fuel monotonicity for the clocked stateful-FFI evaluators

The clocked half of issue #659. The unclocked evaluators are covered by
`SteppedFlapjack.PanValueFfiFuel` in stepped-flapjack, which was
`Flapjack.PanValueFfiFuel` (PR #662) until #1251 moved it. This file states
the same thing for the explicit-clock evaluators of
`Flapjack.PanValueFfiClockSemantics`: a successful run is unchanged -- same
outcome, same clock -- by any larger fuel.

Fuel and clock are different budgets and only the fuel is varied here. Fuel is
the recursion depth the evaluator is allowed; the clock is the resource the
program itself spends, and it is part of the result, so it must be preserved
exactly rather than relaxed.

Only the cases whose body mentions the fuel need an argument; the rest are one
wildcard alternative, so adding a `Prog` constructor does not renumber a list
of `case` names here. The clocked evaluator needs 12 alternatives against the
unclocked one's 25, because it routes most constructors through
`evalPanValueFfiClockLeaf`.

Added by pirapira/flapjack#659.
-/

namespace Flapjack

/-- Monotonicity statement for the clocked call evaluator (`motive1`). -/
def CallClockMono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) (preserveReturnLocals : Bool) : Prop :=
  ∀ fuel' result, fuel ≤ fuel' →
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
      function arguments ma c mh (preserveReturnLocals := preserveReturnLocals) = some result →
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock info
      function arguments ma c mh (preserveReturnLocals := preserveReturnLocals) = some result

/-- Monotonicity statement for the clocked program evaluator (`motive2`). -/
def ProgClockMono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) : Prop :=
  ∀ fuel' result, fuel ≤ fuel' →
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
      ma c mh = some result →
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock program
      ma c mh = some result

/-- The successor case of the clocked call evaluator, as a standalone lemma:
shared between `evalPanValueFfiClockProg_fuel_mono`'s `case2` and
`evalPanValueFfiClockCall_fuel_mono`, which differ only in where the two
program-evaluator induction hypotheses come from. -/
theorem call_clock_succ_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) (preserveReturnLocals : Bool)
    (ihBody : ∀ (body : Prog α) (calleeLocals : VarName → Option (PanValue α)),
      ProgClockMono context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel calleeLocals globals memory ffi (clock - 1) body ma c mh)
    (ihHandler : ∀ (calleeClock : Nat) (calleeGlobals : VarName → Option (PanValue α))
      (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
      (value : PanValue α) (handlerVariable : VarName)
      (handlerProgram : Prog α),
      ProgClockMono context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel (updatePanValueMap locals handlerVariable value) calleeGlobals
        calleeMemory calleeFfi calleeClock handlerProgram ma c mh) :
    CallClockMono context primitive handler structs functions baseAddress topAddress
      bytesInWord (fuel + 1) locals globals memory ffi clock info function arguments ma c mh
      preserveReturnLocals := by
  intro fuel' result hle h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCall] at h
  rw [evalPanValueFfiClockCall]
  cases hargs : panValueCallArgumentsValue structs baseAddress topAddress bytesInWord
      locals globals memory arguments ma with
  | none => simp only [hargs, Option.elim_none] at h ⊢; exact h
  | some values =>
    simp only [hargs, Option.elim_some] at h ⊢
    cases htarget : panValueCallTarget structs c function functions values with
    | none => rw [htarget] at h; simp only [Option.elim_none] at h ⊢; exact h
    | some target =>
          obtain ⟨body, calleeLocals⟩ := target
          rw [htarget] at h
          simp only [Option.elim_some] at h ⊢
          by_cases hclock : clock = 0
          · rw [if_pos hclock] at h ⊢; exact h
          · rw [if_neg hclock] at h ⊢
            cases hbody : evalPanValueFfiClockProg context primitive handler structs
                functions baseAddress topAddress bytesInWord fuel calleeLocals globals
                memory ffi (clock - 1) body ma c mh with
            | none => rw [hbody] at h; simp at h
            | some rp =>
              obtain ⟨outcome, calleeClock⟩ := rp
              rw [hbody] at h
              rw [ihBody body calleeLocals _ _ hfk hbody]
              cases outcome with
              | timeout l cg cm cf => exact h
              | control res =>
                cases res with
                | normal l cg cm cf => exact h
                | broke l cg cm cf => exact h
                | continued l cg cm cf => exact h
                | returned l cg cm cf vs => exact h
                | finalFfi l cg cm cf ev => exact h
                | error l cg cm cf => exact h
                | raised l cg cm cf e v =>
                  simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
                  by_cases hev :
                      (panValueExceptionValid structs c e v &&
                        panValuePayloadWithinLimit structs v) = true
                  · rw [if_pos hev] at h ⊢
                    cases info with
                    | none => exact h
                    | some pr =>
                      obtain ⟨destination, handlerInfo⟩ := pr
                      cases handlerInfo with
                      | none => exact h
                      | some triple =>
                        obtain ⟨caught, handlerVariable, handlerProgram⟩ := triple
                        dsimp only at h ⊢
                        by_cases hcaught : (caught == e) = true
                        · rw [if_pos hcaught] at h ⊢
                          by_cases hhv :
                              panValueHandlerValid structs c locals handlerVariable v
                          · rw [if_pos hhv] at h ⊢
                            exact ihHandler _ _ _ _ _ _ _ _ _ hfk h
                          · rw [if_neg hhv] at h; simp at h
                        · rw [if_neg hcaught] at h ⊢; exact h
                  · rw [if_neg hev] at h; simp at h

theorem evalPanValueFfiClockProg_fuel_mono'
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    : ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)),
    ProgClockMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel locals globals memory ffi clock program ma c mh := by
  intro fuel locals globals memory ffi clock program ma c mh
  induction fuel, locals, globals, memory, ffi, clock, program, ma, c, mh using
    evalPanValueFfiClockProg.induct
    (motive1 := fun fuel locals globals memory ffi clock info function arguments ma c mh preserveReturnLocals =>
      CallClockMono context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel locals globals memory ffi clock info function arguments ma c mh
        preserveReturnLocals) with
  | case1 =>
    intro fuel' result hle h
    rw [evalPanValueFfiClockCall] at h
    simp at h
  | case2 fuel locals globals memory ffi clock info function arguments ma c mh preserveReturnLocals
      ihBody ihHandler =>
    exact call_clock_succ_mono context primitive handler structs functions baseAddress
      topAddress bytesInWord fuel locals globals memory ffi clock info function arguments
      ma c mh preserveReturnLocals ihBody ihHandler
  | case3 =>
    intro fuel' result hle h
    rw [evalPanValueFfiClockProg] at h
    simp at h
  | case4 fuel locals globals memory ffi clock name shape valueExp body ma c mh ihBody =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hv : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord valueExp ma with
    | none =>
      simp only [panValueDecAcceptedValue, evalPanValueExpWith_none, hv, Option.elim_none] at h ⊢
      exact h
    | some value =>
      simp only [panValueDecAcceptedValue, evalPanValueExpWith_none, hv] at h ⊢
      by_cases hshape : panShapeMatches (panValueShape structs value) shape
      · simp only [hshape, if_true, Option.elim_some,
          Option.bind_eq_bind] at h ⊢
        cases hb : evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
            globals memory ffi clock body ma c mh with
        | none => rw [hb] at h; simp at h
        | some q =>
          rw [hb] at h
          rw [ihBody value _ _ hfk hb]
          exact h
      · simp only [hshape] at h ⊢
        exact h
  | case5 fuel locals globals memory ffi clock first second ma c mh ihFirst ihSecond =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hf : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first ma c mh with
    | none => rw [hf] at h; simp at h
    | some p =>
      obtain ⟨firstOutcome, firstClock⟩ := p
      rw [hf] at h
      rw [ihFirst _ _ hfk hf]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases firstOutcome with
      | control r =>
        cases r with
        | normal l g m f =>
          dsimp only at h ⊢
          cases hs : evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel l g m f firstClock second ma c mh with
          | none => rw [hs] at h; simp at h
          | some q =>
            rw [hs] at h
            rw [ihSecond _ _ _ _ _ _ _ hfk hs]
            exact h
        | returned l g m f vs => exact h
        | raised l g m f e v => exact h
        | broke l g m f => exact h
        | continued l g m f => exact h
        | error l g m f => exact h
        | finalFfi l g m f ev => exact h
      | timeout l g m f => exact h
  | case6 fuel locals globals memory ffi clock condition thenBranch elseBranch ma c mh
      ihBranch =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hv : panValueIteConditionValue structs baseAddress topAddress bytesInWord
        locals globals memory condition ma with
    | none =>
      simp only [hv, Option.elim_none] at h ⊢
      exact h
    | some w =>
      simp only [hv, Option.elim_some] at h ⊢
      exact ihBranch _ _ _ hfk h
  | case7 fuel locals globals memory ffi clock info function arguments ma c mh ihCall =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    exact ihCall _ _ hfk h
  | case8 fuel locals globals memory ffi clock name shape function arguments body ma c mh
      ihCall ihBody =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hcall : evalPanValueFfiClockCall context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock none
        function arguments ma c mh (preserveReturnLocals := true) with
    | none => rw [hcall] at h; simp at h
    | some p =>
      obtain ⟨callOutcome, callClock⟩ := p
      rw [hcall] at h
      rw [ihCall _ _ hfk hcall]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases callOutcome with
      | control r =>
        cases r with
        | returned l g m f vs =>
          cases vs with
          | nil => simp at h
          | cons value rest =>
            cases rest with
            | cons _ _ => simp at h
            | nil =>
              dsimp only at h ⊢
              by_cases hshape : panShapeMatches (panValueShape structs value) shape
              · rw [if_pos hshape] at h ⊢
                cases hb : evalPanValueFfiClockProg context primitive handler structs
                  functions baseAddress topAddress bytesInWord fuel
                  (updatePanValueMap locals name value) g m f callClock body ma c mh with
                | none => rw [hb] at h; simp at h
                | some q =>
                  rw [hb] at h
                  rw [ihBody _ _ _ _ _ _ _ hfk hb]
                  exact h
              · rw [if_neg hshape] at h ⊢
                exact h
        | raised l g m f e v => exact h
        | normal l g m f => dsimp only at h ⊢; exact h
        | broke l g m f => dsimp only at h ⊢; exact h
        | continued l g m f => dsimp only at h ⊢; exact h
        | error l g m f => exact h
        | finalFfi l g m f ev => exact h
      | timeout l g m f => exact h
  | case9 fuel locals globals memory ffi clock conditionExp body ma c mh ihBody ihLoop =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hv : panValueIteConditionValue structs baseAddress topAddress bytesInWord
        locals globals memory conditionExp ma with
    | none =>
      simp only [hv, Option.elim_none] at h ⊢
      exact h
    | some cv =>
      simp only [hv, Option.elim_some] at h ⊢
      by_cases hz : (cv == 0) = true
      · rw [if_pos hz] at h ⊢; exact h
      · rw [if_neg hz] at h ⊢
        by_cases hclock : (clock == 0) = true
        · rw [if_pos hclock] at h ⊢; exact h
        · rw [if_neg hclock] at h ⊢
          cases hb : evalPanValueFfiClockProg context primitive handler structs functions
            baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock - 1)
              body ma c mh with
          | none => rw [hb] at h; simp at h
          | some bodyPair =>
            obtain ⟨bodyOutcome, bodyClock⟩ := bodyPair
            rw [hb] at h
            rw [ihBody _ _ hfk hb]
            simp [Option.bind_some] at h ⊢
            cases bodyOutcome with
            | control r =>
              cases r with
              | normal l g m f =>
                dsimp only at h ⊢
                cases hl : evalPanValueFfiClockProg context primitive handler structs
                  functions baseAddress topAddress bytesInWord fuel l g m f bodyClock
                    (Prog.while conditionExp body) ma c mh with
                | none => rw [hl] at h; simp at h
                | some loopPair =>
                  rw [hl] at h
                  rw [ihLoop _ _ _ _ _ _ _ hfk hl]
                  exact h
              | continued l g m f =>
                dsimp only at h ⊢
                cases hl : evalPanValueFfiClockProg context primitive handler structs
                  functions baseAddress topAddress bytesInWord fuel l g m f bodyClock
                    (Prog.while conditionExp body) ma c mh with
                | none => rw [hl] at h; simp at h
                | some loopPair =>
                  rw [hl] at h
                  rw [ihLoop _ _ _ _ _ _ _ hfk hl]
                  exact h
              | returned l g m f vs => exact h
              | raised l g m f e v => exact h
              | broke l g m f => exact h
              | finalFfi l g m f ev => exact h
              | error l g m f => exact h
            | timeout l g m f => exact h
  | case10 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    exact h
  | case11 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    exact h
  | case12 =>
    -- the leaf delegation: every remaining constructor goes through
    -- `evalPanValueFfiClockLeaf`, which does not mention the fuel at all.
    all_goals intro fuel' result hle h
    all_goals obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    all_goals rw [evalPanValueFfiClockProg] at h ⊢
    all_goals first
      | exact h
      | assumption

/-- Fuel monotonicity for the clocked call evaluator, from
`evalPanValueFfiClockProg_fuel_mono'`. -/
theorem evalPanValueFfiClockCall_fuel_mono'
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    : ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)),
    CallClockMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel locals globals memory ffi clock info function arguments ma c mh false := by
  intro fuel locals globals memory ffi clock info function arguments ma c mh
  cases fuel with
  | zero =>
    intro fuel' result hle h
    rw [evalPanValueFfiClockCall] at h
    simp at h
  | succ n =>
    exact call_clock_succ_mono context primitive handler structs functions baseAddress
      topAddress bytesInWord n locals globals memory ffi clock info function arguments ma c mh false
      (fun body calleeLocals => evalPanValueFfiClockProg_fuel_mono' context primitive
        handler structs functions baseAddress topAddress bytesInWord n calleeLocals globals
        memory ffi (clock - 1) body ma c mh)
      (fun calleeClock cg cm cf value hv hp => evalPanValueFfiClockProg_fuel_mono' context
        primitive handler structs functions baseAddress topAddress bytesInWord n
        (updatePanValueMap locals hv value) cg cm cf calleeClock hp ma c mh)

/-! ## The ergonomic forms -/

/-- **Fuel monotonicity for the clocked program evaluator.** -/
theorem evalPanValueFfiClockProg_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    {fuel fuel' : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hfuel : fuel ≤ fuel')
    (hrun : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
      ma c mh = some result) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock program
      ma c mh = some result :=
  evalPanValueFfiClockProg_fuel_mono' context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program ma c mh
    fuel' result hfuel hrun

/-- **Fuel monotonicity for the clocked call evaluator.** -/
theorem evalPanValueFfiClockCall_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    {fuel fuel' : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hfuel : fuel ≤ fuel')
    (hrun : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
      function arguments ma c mh = some result) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock info
      function arguments ma c mh = some result :=
  evalPanValueFfiClockCall_fuel_mono' context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info function
    arguments ma c mh fuel' result hfuel hrun

/-! Fuel monotonicity needed by the state-owned source-code evaluator.  This is
    Flapjack-specific infrastructure: HOL's semantics has no meta-level fuel
    parameter, so these lemmas have no direct HOL declaration. -/
def PanValueFfiClockCodeProgFuelMono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat) : Prop :=
  ∀ (fuel' : Nat) (result : PanValueFfiClockResult α σ), fuel ≤ fuel' →
    ∀ (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
      (program : Prog α) (ma : Option (PanValueMemoryAccess α))
      (contracts : Option PanValueCallContracts)
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel locals globals
        memory ffi clock program ma contracts memoryHandler = some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock program ma contracts memoryHandler = some result

def PanValueFfiClockCodeCallFuelMono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat) : Prop :=
  ∀ (fuel' : Nat) (result : PanValueFfiClockResult α σ), fuel ≤ fuel' →
    ∀ (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
      (info : Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)))
      (function : FunName) (arguments : List (Exp α))
      (ma : Option (PanValueMemoryAccess α))
      (contracts : Option PanValueCallContracts)
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
      (preserveReturnLocals : Bool),
      evalPanValueFfiClockCodeCall context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel locals globals
        memory ffi clock info function arguments ma contracts memoryHandler
        (preserveReturnLocals := preserveReturnLocals) = some result →
      evalPanValueFfiClockCodeCall context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock info function arguments ma contracts memoryHandler
        (preserveReturnLocals := preserveReturnLocals) = some result

def PanValueFfiClockCodeDecCallFuelMono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat) : Prop :=
  ∀ (fuel' : Nat) (result : PanValueFfiClockResult α σ), fuel ≤ fuel' →
    ∀ (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
      (name : VarName) (shape : Shape) (function : FunName)
      (arguments : List (Exp α)) (body : Prog α)
      (ma : Option (PanValueMemoryAccess α))
      (contracts : Option PanValueCallContracts)
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeDecCall context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel locals globals
        memory ffi clock name shape function arguments body ma contracts
        memoryHandler = some result →
      evalPanValueFfiClockCodeDecCall context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock name shape function arguments body ma contracts
        memoryHandler = some result

theorem evalPanValueFfiClockCodeProg_fuel_mono_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) :
    PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord 0 := by
  intro fuel' result hle locals globals memory ffi clock program ma contracts memoryHandler h
  rw [evalPanValueFfiClockCodeProg] at h
  cases h

theorem evalPanValueFfiClockCodeDecCall_fuel_mono_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) :
    PanValueFfiClockCodeDecCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord 0 := by
  intro fuel' result hle locals globals memory ffi clock name shape function arguments body
    ma contracts memoryHandler h
  rw [evalPanValueFfiClockCodeDecCall] at h
  cases h

theorem evalPanValueFfiClockCodeCall_fuel_mono_succ
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (preserveReturnLocals : Bool)
    (ihBody : PanValueFfiClockCodeProgFuelMono context primitive handler structs
      code exceptionShapes baseAddress topAddress bytesInWord fuel) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      evalPanValueFfiClockCodeCall context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock info function arguments ma contracts memoryHandler
        (preserveReturnLocals := preserveReturnLocals) = some result →
      evalPanValueFfiClockCodeCall context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock info function arguments ma contracts memoryHandler
        (preserveReturnLocals := preserveReturnLocals) = some result := by
  intro fuel' result hle h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeCall] at h
  rw [evalPanValueFfiClockCodeCall]
  cases hargs : panValueCallArgumentsValue structs baseAddress topAddress bytesInWord
      locals globals memory arguments ma with
  | none => simp only [hargs, Option.elim_none] at h ⊢; exact h
  | some values =>
      simp only [hargs, Option.elim_some] at h ⊢
      cases htarget : lookupPanSemCodeCall structs code function values with
      | none => rw [htarget] at h; simp only [Option.elim_none] at h ⊢; exact h
      | some target =>
          obtain ⟨body, returnShape, calleeLocals⟩ := target
          rw [htarget] at h
          simp only [Option.elim_some] at h ⊢
          by_cases hclock : clock = 0
          · rw [if_pos hclock] at h ⊢; exact h
          · rw [if_neg hclock] at h ⊢
            cases hbody : evalPanValueFfiClockCodeProg context primitive handler structs
                code exceptionShapes baseAddress topAddress bytesInWord fuel calleeLocals
                globals memory ffi (decPanClock clock) body ma contracts memoryHandler with
            | none => rw [hbody] at h; simp at h
            | some pair =>
                obtain ⟨outcome, calleeClock⟩ := pair
                rw [hbody] at h
                have hbody' := ihBody (fuel' := k) (result := (outcome, calleeClock))
                  hfk calleeLocals globals memory ffi (decPanClock clock) body ma contracts
                  memoryHandler hbody
                rw [hbody'] at ⊢
                cases outcome with
                | timeout l cg cm cf => simpa using h
                | control res =>
                    cases res with
                    | normal l cg cm cf => simpa using h
                    | broke l cg cm cf => simpa using h
                    | continued l cg cm cf => simpa using h
                    | error l cg cm cf => simpa using h
                    | finalFfi l cg cm cf event => simpa using h
                    | returned calleeLocals cg cm cf values =>
                        cases values with
                        | nil => simp_all
                        | cons value rest =>
                            cases rest with
                            | cons value2 rest => simpa using h
                            | nil => simpa using h
                    | raised calleeLocals cg cm cf exception value =>
                        simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
                        cases info with
                        | none => simpa using h
                        | some infoPair =>
                            cases infoPair with
                            | mk destination handlerInfo =>
                                cases handlerInfo with
                                | none => simpa using h
                                | some handlerTuple =>
                                    obtain ⟨caught, handlerVariable, handlerProgram⟩ := handlerTuple
                                    by_cases hcaught : (caught == exception) = true
                                    · simp [hcaught] at h ⊢
                                      cases hexShape : exceptionShapes exception with
                                      | none => simpa [hexShape] using h
                                      | some shape =>
                                          by_cases hvalid :
                                              panShapeMatches (panValueShape structs value) shape = true ∧
                                                panValueAssignmentValid structs locals (fun _ => none)
                                                  .local handlerVariable value = true
                                          · simp only [hexShape] at h ⊢
                                            rw [if_pos hvalid] at h ⊢
                                            exact ihBody (fuel' := k) (result := result) hfk
                                              (updatePanValueMap locals handlerVariable value)
                                              cg cm cf (min (decPanClock clock) calleeClock)
                                              handlerProgram ma contracts memoryHandler h
                                          · simp only [hexShape] at h ⊢
                                            rw [if_neg hvalid] at h ⊢
                                            exact h
                                    · simpa [hcaught] using h

theorem evalPanValueFfiClockCodeCall_fuel_mono_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) :
    PanValueFfiClockCodeCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord 0 := by
  intro fuel' result hle locals globals memory ffi clock info function arguments ma
    contracts memoryHandler preserveReturnLocals h
  rw [evalPanValueFfiClockCodeCall] at h
  cases h

theorem evalPanValueFfiClockCodeCall_fuel_mono_succ_all
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ih : PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    PanValueFfiClockCodeCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) := by
  intro fuel' result hle locals globals memory ffi clock info function arguments ma
    contracts memoryHandler preserveReturnLocals h
  exact evalPanValueFfiClockCodeCall_fuel_mono_succ context primitive handler structs
    code exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory
    ffi clock info function arguments ma contracts memoryHandler preserveReturnLocals ih
    fuel' result hle h

theorem evalPanValueFfiClockCodeDecCall_fuel_mono_succ
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihProg : PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel)
    (ihCall : PanValueFfiClockCodeCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    PanValueFfiClockCodeDecCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) := by
  intro fuel' result hle locals globals memory ffi clock name shape function arguments body
    ma contracts memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeDecCall] at h
  rw [evalPanValueFfiClockCodeDecCall]
  cases hcall : evalPanValueFfiClockCodeCall context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      none function arguments ma contracts memoryHandler true with
  | none => rw [hcall] at h; simp at h
  | some pair =>
      obtain ⟨outcome, nextClock⟩ := pair
      rw [hcall] at h
      have hcall' := ihCall k (outcome, nextClock) hfk
        locals globals memory ffi clock none function arguments ma contracts memoryHandler true hcall
      rw [hcall'] at ⊢
      cases outcome with
      | timeout nextLocals nextGlobals nextMemory nextFfi => simpa using h
      | control result =>
          cases result with
          | normal nextLocals nextGlobals nextMemory nextFfi => simpa using h
          | broke nextLocals nextGlobals nextMemory nextFfi => simpa using h
          | continued nextLocals nextGlobals nextMemory nextFfi => simpa using h
          | error nextLocals nextGlobals nextMemory nextFfi => simpa using h
          | finalFfi nextLocals nextGlobals nextMemory nextFfi event => simpa using h
          | raised nextLocals nextGlobals nextMemory nextFfi exception value => simpa using h
          | returned nextLocals nextGlobals nextMemory nextFfi values =>
              cases values with
              | nil => simp_all
              | cons value rest =>
                  cases rest with
                  | cons value2 rest => simp_all
                  | nil =>
                      by_cases hshape : panShapeMatches (panValueShape structs value) shape
                          = true
                      · cases hbody : evalPanValueFfiClockCodeProg context primitive handler
                            structs code exceptionShapes baseAddress topAddress bytesInWord fuel
                            (updatePanValueMap locals name value) nextGlobals nextMemory nextFfi
                            nextClock body ma contracts memoryHandler with
                        | none => simp [hshape, hbody] at h
                        | some bodyPair =>
                            have hbody' := ihProg (fuel' := k) (result := bodyPair) hfk
                              (updatePanValueMap locals name value) nextGlobals nextMemory nextFfi
                              nextClock body ma contracts memoryHandler hbody
                            simpa [hbody, hbody'] using h
                      · simpa [evalPanValueFfiClockCodeDecCall, hcall, hcall', hshape] using h

/-- The source-program `Call` constructor preserves fuel monotonicity by the
    state-owned CodeCall evaluator. This is Flapjack-specific fuel plumbing;
    HOL `evaluate_def` has no meta-level fuel parameter. -/
theorem evalPanValueFfiClockCodeProg_call_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihCall : PanValueFfiClockCodeCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (info : Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)))
        (function : FunName) (arguments : List (Exp α))
        (ma : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock (.call info function arguments) ma contracts memoryHandler = some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock (.call info function arguments) ma contracts memoryHandler = some result := by
  intro fuel' result hle locals globals memory ffi clock info function arguments ma contracts
    memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeProg] at h
  rw [evalPanValueFfiClockCodeProg]
  exact ihCall k result hfk locals globals memory ffi clock info function arguments ma
    contracts memoryHandler false h

/-- Flapjack-specific fuel plumbing for the source-program `If` constructor:
    monotonicity follows through the selected state-owned recursive branch.
    HOL's semantics has no meta-level fuel parameter, so this helper has no
    direct HOL declaration. -/
theorem evalPanValueFfiClockCodeProg_ite_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihProg : PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (condition : Exp α) (thenBranch elseBranch : Prog α)
        (ma : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock (.ite condition thenBranch elseBranch) ma contracts memoryHandler =
          some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock (.ite condition thenBranch elseBranch) ma contracts memoryHandler =
          some result := by
  intro fuel' result hle locals globals memory ffi clock condition thenBranch elseBranch ma
    contracts memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeProg] at h
  rw [evalPanValueFfiClockCodeProg]
  cases hcondition : panValueIteConditionValue structs baseAddress topAddress bytesInWord
      locals globals memory condition ma with
  | none => simp [hcondition] at h ⊢; exact h
  | some conditionValue =>
      by_cases hnonzero : conditionValue != 0
      · simp [hcondition, hnonzero] at h ⊢
        exact ihProg k result hfk locals globals memory ffi clock thenBranch ma contracts
          memoryHandler h
      · simp [hcondition, hnonzero] at h ⊢
        exact ihProg k result hfk locals globals memory ffi clock elseBranch ma contracts
          memoryHandler h

/-- Flapjack-specific fuel plumbing for the source-program `Seq` constructor.
    The recursive calls preserve the exact `fixPanClock`-adjusted first result
    and then use monotonicity for the second program. HOL's semantics has no
    meta-level fuel parameter, so this helper has no direct HOL declaration. -/
theorem evalPanValueFfiClockCodeProg_seq_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihProg : PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (first second : Prog α) (ma : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock (.seq first second) ma contracts memoryHandler = some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock (.seq first second) ma contracts memoryHandler = some result := by
  intro fuel' result hle locals globals memory ffi clock first second ma contracts
    memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeProg] at h
  rw [evalPanValueFfiClockCodeProg]
  cases hfirst : evalPanValueFfiClockCodeProg context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      first ma contracts memoryHandler with
  | none => simp [hfirst] at h
  | some firstPair =>
      obtain ⟨firstOutcome, firstClock⟩ := firstPair
      have hfirst' := ihProg k (firstOutcome, firstClock) hfk locals globals memory ffi clock
        first ma contracts memoryHandler hfirst
      cases firstOutcome with
      | timeout nextLocals nextGlobals nextMemory nextFfi =>
          simpa [evalPanValueFfiClockCodeProg, hfirst, hfirst', fixPanClock] using h
      | control controlResult =>
          cases controlResult with
          | normal nextLocals nextGlobals nextMemory nextFfi =>
              have hsecond :
                  evalPanValueFfiClockCodeProg context primitive handler structs code
                    exceptionShapes baseAddress topAddress bytesInWord fuel nextLocals
                    nextGlobals nextMemory nextFfi (min clock firstClock) second ma contracts
                    memoryHandler = some result := by
                simpa [evalPanValueFfiClockCodeProg, hfirst, fixPanClock] using h
              have hsecond' := ihProg k result hfk nextLocals nextGlobals nextMemory nextFfi
                (min clock firstClock) second ma contracts memoryHandler hsecond
              simp [hfirst', hsecond']
          | broke nextLocals nextGlobals nextMemory nextFfi =>
              simpa [evalPanValueFfiClockCodeProg, hfirst, hfirst', fixPanClock] using h
          | continued nextLocals nextGlobals nextMemory nextFfi =>
              simpa [evalPanValueFfiClockCodeProg, hfirst, hfirst', fixPanClock] using h
          | error nextLocals nextGlobals nextMemory nextFfi =>
              simpa [evalPanValueFfiClockCodeProg, hfirst, hfirst', fixPanClock] using h
          | finalFfi nextLocals nextGlobals nextMemory nextFfi event =>
              simpa [evalPanValueFfiClockCodeProg, hfirst, hfirst', fixPanClock] using h
          | returned nextLocals nextGlobals nextMemory nextFfi values =>
              simpa [evalPanValueFfiClockCodeProg, hfirst, hfirst', fixPanClock] using h
          | raised nextLocals nextGlobals nextMemory nextFfi exception value =>
              simpa [evalPanValueFfiClockCodeProg, hfirst, hfirst', fixPanClock] using h

/-- Flapjack-specific fuel plumbing for source `While`: preserve the body
    result, apply `fixPanClock`, and use the recursive-program hypothesis for
    the next loop iteration. HOL's semantics has no meta-level fuel parameter,
    so this helper has no direct HOL declaration. -/
theorem evalPanValueFfiClockCodeProg_while_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihProg : PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (condition : Exp α) (body : Prog α)
        (ma : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock (.while condition body) ma contracts memoryHandler = some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock (.while condition body) ma contracts memoryHandler = some result := by
  intro fuel' result hle locals globals memory ffi clock condition body ma contracts
    memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeProg] at h
  rw [evalPanValueFfiClockCodeProg]
  cases hcondition : panValueIteConditionValue structs baseAddress topAddress bytesInWord
      locals globals memory condition ma with
  | none => simp [hcondition] at h ⊢; exact h
  | some conditionValue =>
      by_cases hcondZero : conditionValue == 0
      · simp [hcondition, hcondZero] at h ⊢; exact h
      · by_cases hclock : clock == 0
        · simp [hcondition, hcondZero, hclock] at h ⊢; exact h
        · simp [hcondition, hcondZero, hclock] at h ⊢
          cases hbody : evalPanValueFfiClockCodeProg context primitive handler structs code
              exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory ffi
              (decPanClock clock) body ma contracts memoryHandler with
          | none => simp [hbody] at h
          | some bodyPair =>
              obtain ⟨bodyOutcome, bodyClock⟩ := bodyPair
              have hbody' := ihProg k (bodyOutcome, bodyClock) hfk locals globals memory ffi
                (decPanClock clock) body ma contracts memoryHandler hbody
              cases bodyOutcome with
              | timeout nextLocals nextGlobals nextMemory nextFfi =>
                  simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                    hbody, hbody', fixPanClock] using h
              | control controlResult =>
                  cases controlResult with
                  | normal nextLocals nextGlobals nextMemory nextFfi =>
                      have hloop :
                          evalPanValueFfiClockCodeProg context primitive handler structs code
                            exceptionShapes baseAddress topAddress bytesInWord fuel nextLocals
                            nextGlobals nextMemory nextFfi (min (decPanClock clock) bodyClock)
                            (.while condition body) ma contracts memoryHandler = some result := by
                        simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                          hbody, fixPanClock] using h
                      have hloop' := ihProg k result hfk nextLocals nextGlobals nextMemory
                        nextFfi (min (decPanClock clock) bodyClock) (.while condition body) ma
                        contracts memoryHandler hloop
                      simp [hbody', hloop']
                  | continued nextLocals nextGlobals nextMemory nextFfi =>
                      have hloop :
                          evalPanValueFfiClockCodeProg context primitive handler structs code
                            exceptionShapes baseAddress topAddress bytesInWord fuel nextLocals
                            nextGlobals nextMemory nextFfi (min (decPanClock clock) bodyClock)
                            (.while condition body) ma contracts memoryHandler = some result := by
                        simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                          hbody, fixPanClock] using h
                      have hloop' := ihProg k result hfk nextLocals nextGlobals nextMemory
                        nextFfi (min (decPanClock clock) bodyClock) (.while condition body) ma
                        contracts memoryHandler hloop
                      simp [hbody', hloop']
                  | broke nextLocals nextGlobals nextMemory nextFfi =>
                      simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                        hbody, hbody', fixPanClock] using h
                  | error nextLocals nextGlobals nextMemory nextFfi =>
                      simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                        hbody, hbody', fixPanClock] using h
                  | finalFfi nextLocals nextGlobals nextMemory nextFfi event =>
                      simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                        hbody, hbody', fixPanClock] using h
                  | returned nextLocals nextGlobals nextMemory nextFfi values =>
                      simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                        hbody, hbody', fixPanClock] using h
                  | raised nextLocals nextGlobals nextMemory nextFfi exception value =>
                      simpa [evalPanValueFfiClockCodeProg, hcondition, hcondZero, hclock,
                        hbody, hbody', fixPanClock] using h

/-- Flapjack-specific fuel plumbing for source `Dec`: the accepted value and
    local update are fuel-independent, leaving the recursive body IH. HOL's
    semantics has no meta-level fuel parameter, so this helper has no direct
    HOL declaration. -/
theorem evalPanValueFfiClockCodeProg_dec_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihProg : PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
        (ma : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock (.dec name shape value body) ma contracts memoryHandler = some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock (.dec name shape value body) ma contracts memoryHandler = some result := by
  intro fuel' result hle locals globals memory ffi clock name shape value body ma contracts
    memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeProg] at h
  rw [evalPanValueFfiClockCodeProg]
  cases hvalue : panValueDecAcceptedValue structs baseAddress topAddress bytesInWord locals
      globals memory value ma shape with
  | none => simp [hvalue] at h ⊢; exact h
  | some evaluated =>
      cases hbody : evalPanValueFfiClockCodeProg context primitive handler structs code
          exceptionShapes baseAddress topAddress bytesInWord fuel
          (updatePanValueMap locals name evaluated) globals memory ffi clock body ma contracts
          memoryHandler with
      | none => simp [hvalue, hbody] at h
      | some bodyPair =>
          have hbody' := ihProg k bodyPair hfk
            (updatePanValueMap locals name evaluated) globals memory ffi clock body ma contracts
            memoryHandler hbody
          simpa [evalPanValueFfiClockCodeProg, hvalue, hbody, hbody'] using h

/-- Flapjack-specific fuel plumbing: the source-program `DecCall` constructor
    delegates to the state-owned DecCall evaluator, whose continuation case is
    covered by its helper theorem. HOL's semantics has no meta-level fuel
    parameter, so this helper has no direct HOL declaration. -/
theorem evalPanValueFfiClockCodeProg_decCall_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihDecCall : PanValueFfiClockCodeDecCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (name : VarName) (shape : Shape) (function : FunName)
        (arguments : List (Exp α)) (body : Prog α)
        (ma : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock (.decCall name shape function arguments body) ma contracts
        memoryHandler = some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock (.decCall name shape function arguments body) ma contracts
        memoryHandler = some result := by
  intro fuel' result hle locals globals memory ffi clock name shape function arguments body ma
    contracts memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCodeProg] at h
  rw [evalPanValueFfiClockCodeProg]
  exact ihDecCall k result hfk locals globals memory ffi clock name shape function arguments
    body ma contracts memoryHandler h

/-- Flapjack-specific fuel plumbing for the source-program `raise` equation,
    which does not recurse on the fuel. HOL's semantics has no meta-level fuel
    parameter, so this helper has no direct HOL declaration. -/
theorem evalPanValueFfiClockCodeProg_raise_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat) :
    ∀ fuel' result, fuel + 1 ≤ fuel' →
      ∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
        (exception : ExceptionId) (value : Exp α)
        (ma : Option (PanValueMemoryAccess α))
        (contracts : Option PanValueCallContracts)
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
        memory ffi clock (.raise exception value) ma contracts memoryHandler = some result →
      evalPanValueFfiClockCodeProg context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel' locals globals
        memory ffi clock (.raise exception value) ma contracts memoryHandler = some result := by
  intro fuel' result hle locals globals memory ffi clock exception value ma contracts
    memoryHandler h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  rw [evalPanValueFfiClockCodeProg] at h
  rw [evalPanValueFfiClockCodeProg]
  exact h

/-- One-step successor monotonicity for the state-owned source-program
    evaluator, assembled from its constructor lemmas. This is Flapjack fuel
    infrastructure rather than a HOL theorem: the HOL evaluator is not
    fuel-indexed. -/
theorem evalPanValueFfiClockCodeProg_fuel_mono_succ_all
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (ihProg : PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel)
    (ihCall : PanValueFfiClockCodeCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel)
    (ihDecCall : PanValueFfiClockCodeDecCallFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel) :
    PanValueFfiClockCodeProgFuelMono context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) := by
  intro fuel' result hle locals globals memory ffi clock program ma contracts memoryHandler h
  cases program with
  | skip =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | dec name shape value body =>
      exact evalPanValueFfiClockCodeProg_dec_fuel_mono context primitive handler structs
        code exceptionShapes baseAddress topAddress bytesInWord fuel ihProg fuel' result hle
        locals globals memory ffi clock name shape value body ma contracts memoryHandler h
  | assign kind name value =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | primitive name operator args =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | store address value =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | store32 address value =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | storeByte address value =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | seq first second =>
      exact evalPanValueFfiClockCodeProg_seq_fuel_mono context primitive handler structs
        code exceptionShapes baseAddress topAddress bytesInWord fuel ihProg fuel' result hle
        locals globals memory ffi clock first second ma contracts memoryHandler h
  | ite condition thenBranch elseBranch =>
      exact evalPanValueFfiClockCodeProg_ite_fuel_mono context primitive handler structs
        code exceptionShapes baseAddress topAddress bytesInWord fuel ihProg fuel' result hle
        locals globals memory ffi clock condition thenBranch elseBranch ma contracts
        memoryHandler h
  | «while» condition body =>
      exact evalPanValueFfiClockCodeProg_while_fuel_mono context primitive handler structs
        code exceptionShapes baseAddress topAddress bytesInWord fuel ihProg fuel' result hle
        locals globals memory ffi clock condition body ma contracts memoryHandler h
  | «break» =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | «continue» =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | call info name args =>
      exact evalPanValueFfiClockCodeProg_call_fuel_mono context primitive handler structs
        code exceptionShapes baseAddress topAddress bytesInWord fuel ihCall fuel' result hle
        locals globals memory ffi clock info name args ma contracts memoryHandler h
  | decCall name shape function args body =>
      exact evalPanValueFfiClockCodeProg_decCall_fuel_mono context primitive handler structs
        code exceptionShapes baseAddress topAddress bytesInWord fuel ihDecCall fuel' result hle
        locals globals memory ffi clock name shape function args body ma contracts
        memoryHandler h
  | extCall function configuration configurationLength array arrayLength =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | raise exception value =>
      exact evalPanValueFfiClockCodeProg_raise_fuel_mono context primitive handler structs
        code exceptionShapes baseAddress topAddress bytesInWord fuel fuel' result hle
        locals globals memory ffi clock exception value ma contracts memoryHandler h
  | «return» value =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | shMemLoad size kind name address =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | shMemStore size address value =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | tick =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h
  | annot tag text =>
      cases fuel' with
      | zero => omega
      | succ fuel' => simpa [evalPanValueFfiClockCodeProg] using h

/-- Simultaneous all-fuel monotonicity for the state-owned source evaluator.
    This is a Flapjack theorem about the fuel-indexed implementation, not a
    direct port of HOL semantics, which has no fuel parameter. -/
theorem evalPanValueFfiClockCode_fuel_mono_mutual
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α) :
    ∀ fuel, PanValueFfiClockCodeProgFuelMono context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel ∧
      PanValueFfiClockCodeCallFuelMono context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel ∧
      PanValueFfiClockCodeDecCallFuelMono context primitive handler structs code
        exceptionShapes baseAddress topAddress bytesInWord fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact ⟨evalPanValueFfiClockCodeProg_fuel_mono_zero context primitive handler
        structs code exceptionShapes baseAddress topAddress bytesInWord,
        evalPanValueFfiClockCodeCall_fuel_mono_zero context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord,
        evalPanValueFfiClockCodeDecCall_fuel_mono_zero context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord⟩
  | succ fuel ih =>
      rcases ih with ⟨ihProg, ihCall, ihDecCall⟩
      exact ⟨evalPanValueFfiClockCodeProg_fuel_mono_succ_all context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord fuel
          ihProg ihCall ihDecCall,
        evalPanValueFfiClockCodeCall_fuel_mono_succ_all context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord fuel ihProg,
        evalPanValueFfiClockCodeDecCall_fuel_mono_succ context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord fuel ihProg ihCall⟩

/-- **Fuel monotonicity for the public clocked evaluator.** The clock is
preserved exactly; only the fuel is relaxed. -/
theorem evalPanValueFfiClockProgram_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α) (handler : PanValueStatefulFfiHandler α σ)
    {fuel fuel' : Nat} (hfuel : fuel ≤ fuel') (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    {ma : Option (PanValueMemoryAccess α)}
    {mh : Option (PanValueMemoryFfiHandler α σ)}
    {result : PanValueFfiClockResult α σ}
    (hrun : evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := ma) (memoryHandler := mh) = some result) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel'
      declarations entry arguments (memoryAccess := ma) (memoryHandler := mh) = some result := by
  unfold evalPanValueFfiClockProgram evalPanValueFfiClockProgramCodeCall at hrun ⊢
  cases hstate : evalPanValueDeclarations initial.source declarations (memoryAccess := ma) with
  | none => rw [hstate] at hrun; simp at hrun
  | some state =>
      rw [hstate] at hrun
      simp only [Option.bind_eq_bind, Option.bind_some] at hrun ⊢
      cases hcode : panValueProgramStateCodeMap state with
      | none => rw [hcode] at hrun; simp at hrun
      | some code =>
        simp only [hcode, Option.bind_some] at hrun ⊢
        let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
          state.parameterShapes)
        cases hcall : evalPanValueFfiClockCodeCall context primitive handler state.structs code
            (fun exception => lookupInfo exception state.exceptions) state.baseAddress
            state.topAddress state.bytesInWord fuel (fun _ => none) state.globals state.memory
            initial.ffi clock none entry arguments ma contracts mh with
        | none => rw [hcall] at hrun; simp at hrun
        | some callResult =>
          rw [hcall] at hrun
          have hcall' := ((evalPanValueFfiClockCode_fuel_mono_mutual context primitive handler
            state.structs code (fun exception => lookupInfo exception state.exceptions)
            state.baseAddress state.topAddress state.bytesInWord fuel).2.1)
            fuel' callResult hfuel (fun _ => none) state.globals state.memory initial.ffi clock
            none entry arguments ma contracts mh false hcall
          rw [hcall'] at ⊢
          exact hrun


end Flapjack
