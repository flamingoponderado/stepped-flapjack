import SteppedFlapjack.PanToCrepSteps.CountedDecl

/-! Counted and HOL correspondence for arbitrarily nested scalar declarations. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A return under a list of constant scalar declarations. -/
def countedDeclList (declarations : List (VarName × BitVec 64)) (returned : BitVec 64) : Prog (RiscV.Word 64) :=
  match declarations with
  | [] => .return (.const returned)
  | (name,value)::rest => .dec name .one (.const value) (countedDeclList rest returned)

/-- HOL syntax for the same nested declarations. -/
def countedDeclListHOL (declarations : List (VarName × BitVec 64)) (returned : BitVec 64) : ProgHOL 64 :=
  match declarations with
  | [] => .return (.const returned)
  | (name,value)::rest => .dec (ofString name) .one (.const value) (countedDeclListHOL rest returned)

/-- For any finite list of ranged local names and constant word values, the
counted source run and HOL run agree on the return. Its actual count is
`2 * length + 2` and bounds the HOL control visits. -/
theorem counted_declList_return {σ : Type} (declarations : List (VarName × BitVec 64))
    (returned : BitVec 64) (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    ∀ (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs],
      PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production →
      (∀ item ∈ declarations, NameRanged item.1) → ∀ fuel,
      ∃ result final,
        evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + declarations.length + 1)
          production.locals production.globals production.memory production.ffi (countedDeclList declarations returned)
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,2 * declarations.length + 2) ∧
        source.evaluateHOLFiniteState (countedDeclListHOL declarations returned) =
          (some (.returned (.val (.word returned))),final) ∧
        controlSteps (countedDeclListHOL declarations returned) source ≤ 2 * declarations.length + 2 := by
  induction declarations with
  | nil =>
    intro production source dec rel ranged names fuel
    obtain ⟨exec,run,_,bound⟩ := counted_return_word_related production source rel ranged (.const returned)
      (by simp [ExpByteRanged]) returned (by simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp])
      context primitive handler functions fuel
    exact ⟨_,_,by simpa [countedDeclList,panValueExpStepCost] using exec,
      by simpa [countedDeclListHOL,expToHOL] using run,
      by simpa [countedDeclListHOL,expToHOL,panValueExpStepCost] using bound⟩
  | cons item rest ih =>
    rcases item with ⟨name,value⟩
    intro production source dec rel ranged names fuel
    have nameRanged : NameRanged name := names (name,value) (by simp)
    have restRanged : ∀ item ∈ rest, NameRanged item.1 := by
      intro item member
      exact names item (by simp [member])
    let nextProduction := {production with locals := updatePanValueMap production.locals name (.word value)}
    let nextSource := setVarHOLFinite (ofString name) (.val (.word value)) source
    let nextDec : DecidablePred nextSource.memaddrs := by change DecidablePred source.memaddrs; infer_instance
    have nextRel : PanSemStateRelExec nextProduction nextSource.toExact := by
      simpa [nextProduction,nextSource] using PanSemStateRelExec.updateLocals rel name nameRanged (.word value)
    have nextRanged : PanSemStateRelExecRanged nextProduction := by
      exact PanSemStateRelExecRanged.updateLocals ranged name (.word value) (by simp [PanValueByteRanged])
    obtain ⟨result,final,bodyExec,bodyRun,bodyBound⟩ := @ih nextProduction nextSource nextDec nextRel nextRanged restRanged fuel
    have bodyExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + rest.length + 1)
        (updatePanValueMap production.locals name (.word value)) production.globals production.memory production.ffi
        (countedDeclList rest returned) (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (result,2 * rest.length + 2) := by
      simpa [nextProduction,panSemBitVec64MemoryAccess] using bodyExec
    have initRun : evalPanSemStateExp production (.const value) = some (.word value) := by
      simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
    obtain ⟨exec,run,bound⟩ := counted_decl_word production source final rel ranged name (.const value)
      (by simp [ExpByteRanged]) value initRun context primitive handler functions (fuel + rest.length + 1)
      (countedDeclList rest returned) (countedDeclListHOL rest returned) result
      (some (.returned (.val (.word returned)))) (2 * rest.length + 2) bodyExec' bodyRun bodyBound
    have costEq : panValueExpStepCost (.const value : Exp (RiscV.Word 64)) + (2 * rest.length + 2) + 1 =
        2 * ((name,value)::rest).length + 2 := by simp [panValueExpStepCost]; omega
    have fuelEq : fuel + rest.length + 1 + 1 = fuel + ((name,value)::rest).length + 1 := by simp; omega
    rw [costEq,fuelEq] at exec
    rw [costEq] at bound
    refine ⟨restorePanValueFfiLocal name (production.locals name) result,
      {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_⟩
    · simpa only [countedDeclList] using exec
    · simpa [countedDeclListHOL,expToHOL] using run
    · simpa only [countedDeclListHOL,expToHOL] using bound

/-- Wrap an arbitrary executable body in scalar declarations. -/
def wrapCountedDeclList (declarations : List (VarName × BitVec 64))
    (body : Prog (RiscV.Word 64)) : Prog (RiscV.Word 64) :=
  match declarations with
  | [] => body
  | (name,value)::rest => .dec name .one (.const value) (wrapCountedDeclList rest body)

/-- Wrap the corresponding HOL body in the same scalar declarations. -/
def wrapCountedDeclListHOL (declarations : List (VarName × BitVec 64)) (body : ProgHOL 64) : ProgHOL 64 :=
  match declarations with
  | [] => body
  | (name,value)::rest => .dec (ofString name) .one (.const value) (wrapCountedDeclListHOL rest body)

/-- The executable entry state after installing every declaration. -/
def enterCountedDeclList {σ : Type} : List (VarName × BitVec 64) →
    PanSemState (RiscV.Word 64) (FfiState σ) → PanSemState (RiscV.Word 64) (FfiState σ)
  | [], state => state
  | (name,value)::rest, state =>
      enterCountedDeclList rest {state with locals := updatePanValueMap state.locals name (.word value)}

/-- The HOL entry state after installing every declaration. -/
def enterCountedDeclListHOL {σ : Type} : List (VarName × BitVec 64) →
    PanSemStateFiniteExact 64 σ → PanSemStateFiniteExact 64 σ
  | [], state => state
  | (name,value)::rest, state => enterCountedDeclListHOL rest (setVarHOLFinite (ofString name) (.val (.word value)) state)

/-- A proved body run and its control-visit bound lift through any finite
number of scalar declarations. No particular body syntax or result is required. -/
theorem counted_declList_wrap {σ : Type} (declarations : List (VarName × BitVec 64))
    (body : Prog (RiscV.Word 64)) (bodyHOL : ProgHOL 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    ∀ (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs],
      PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production →
      (∀ item ∈ declarations, NameRanged item.1) →
      ∀ (fuel bodyCost : Nat) (bodyResult : PanValueFfiControlResult (RiscV.Word 64) σ)
        (holResult : Option (PanSemResultExact 64)) (bodyFinal : PanSemStateFiniteExact 64 σ),
      let entry := enterCountedDeclList declarations production
      let exactEntry := enterCountedDeclListHOL declarations source
      evalPanValueFfiProgSteps context primitive handler entry.structs functions entry.baseAddress entry.topAddress
        panSemBitVec64BytesInWord fuel entry.locals entry.globals entry.memory entry.ffi body
        (memoryAccess := some (panSemBitVec64MemoryAccess entry)) = some (bodyResult,bodyCost) →
      exactEntry.evaluateHOLFiniteState bodyHOL = (holResult,bodyFinal) →
      controlSteps bodyHOL exactEntry ≤ bodyCost →
      ∃ result final,
        evalPanValueFfiProgSteps context primitive handler production.structs functions
          production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + declarations.length)
          production.locals production.globals production.memory production.ffi (wrapCountedDeclList declarations body)
          (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,2 * declarations.length + bodyCost) ∧
        source.evaluateHOLFiniteState (wrapCountedDeclListHOL declarations bodyHOL) = (holResult,final) ∧
        controlSteps (wrapCountedDeclListHOL declarations bodyHOL) source ≤ 2 * declarations.length + bodyCost := by
  induction declarations with
  | nil =>
    intro production source dec rel ranged names fuel bodyCost bodyResult holResult bodyFinal entry exactEntry bodyExec bodyRun bodyBound
    dsimp [entry,exactEntry,enterCountedDeclList,enterCountedDeclListHOL] at bodyExec bodyRun bodyBound
    exact ⟨bodyResult,bodyFinal,by simpa [wrapCountedDeclList,enterCountedDeclList] using bodyExec,
      by simpa [wrapCountedDeclListHOL,enterCountedDeclListHOL] using bodyRun,
      by simpa [wrapCountedDeclListHOL,enterCountedDeclListHOL] using bodyBound⟩
  | cons item rest ih =>
    rcases item with ⟨name,value⟩
    intro production source dec rel ranged names fuel bodyCost bodyResult holResult bodyFinal entry exactEntry bodyExec bodyRun bodyBound
    have nameRanged : NameRanged name := names (name,value) (by simp)
    have restRanged : ∀ item ∈ rest, NameRanged item.1 := by
      intro item member
      exact names item (by simp [member])
    let nextProduction := {production with locals := updatePanValueMap production.locals name (.word value)}
    let nextSource := setVarHOLFinite (ofString name) (.val (.word value)) source
    let nextDec : DecidablePred nextSource.memaddrs := by change DecidablePred source.memaddrs; infer_instance
    have nextRel : PanSemStateRelExec nextProduction nextSource.toExact := by
      simpa [nextProduction,nextSource] using PanSemStateRelExec.updateLocals rel name nameRanged (.word value)
    have nextRanged : PanSemStateRelExecRanged nextProduction := by
      exact PanSemStateRelExecRanged.updateLocals ranged name (.word value) (by simp [PanValueByteRanged])
    obtain ⟨result,final,innerExec,innerRun,innerBound⟩ :=
      @ih nextProduction nextSource nextDec nextRel nextRanged restRanged fuel bodyCost bodyResult holResult bodyFinal
        bodyExec bodyRun bodyBound
    have innerExec' : evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel + rest.length)
        (updatePanValueMap production.locals name (.word value)) production.globals production.memory production.ffi
        (wrapCountedDeclList rest body) (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (result,2 * rest.length + bodyCost) := by
      simpa [nextProduction,panSemBitVec64MemoryAccess] using innerExec
    have initRun : evalPanSemStateExp production (.const value) = some (.word value) := by
      simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
    obtain ⟨exec,run,bound⟩ := counted_decl_word production source final rel ranged name (.const value)
      (by simp [ExpByteRanged]) value initRun context primitive handler functions (fuel + rest.length)
      (wrapCountedDeclList rest body) (wrapCountedDeclListHOL rest bodyHOL) result holResult
      (2 * rest.length + bodyCost) innerExec' innerRun innerBound
    have costEq : panValueExpStepCost (.const value : Exp (RiscV.Word 64)) + (2 * rest.length + bodyCost) + 1 =
        2 * ((name,value)::rest).length + bodyCost := by simp [panValueExpStepCost]; omega
    have fuelEq : fuel + rest.length + 1 = fuel + ((name,value)::rest).length := by simp; omega
    rw [costEq,fuelEq] at exec
    rw [costEq] at bound
    refine ⟨restorePanValueFfiLocal name (production.locals name) result,
      {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))},?_,?_,?_⟩
    · simpa only [wrapCountedDeclList] using exec
    · simpa only [wrapCountedDeclListHOL,expToHOL] using run
    · simpa only [wrapCountedDeclListHOL,expToHOL] using bound

/-- Installing scalar declarations preserves the executable/HOL state
relation and byte-rangedness. -/
theorem enterCountedDeclList_rel {σ : Type} (declarations : List (VarName × BitVec 64)) :
    ∀ (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ),
      PanSemStateRelExec production source.toExact → PanSemStateRelExecRanged production →
      (∀ item ∈ declarations, NameRanged item.1) →
      PanSemStateRelExec (enterCountedDeclList declarations production)
        (enterCountedDeclListHOL declarations source).toExact ∧
      PanSemStateRelExecRanged (enterCountedDeclList declarations production) := by
  induction declarations with
  | nil => intro production source rel ranged names; exact ⟨rel,ranged⟩
  | cons item rest ih =>
    rcases item with ⟨name,value⟩
    intro production source rel ranged names
    have nameRanged : NameRanged name := names (name,value) (by simp)
    have restRanged : ∀ item ∈ rest, NameRanged item.1 := by
      intro item member
      exact names item (by simp [member])
    have nextRel := PanSemStateRelExec.updateLocals rel name nameRanged (.word value)
    have nextRanged := PanSemStateRelExecRanged.updateLocals ranged name (.word value) (by simp [PanValueByteRanged])
    exact ih _ _ (by simpa using nextRel) nextRanged restRanged

/-- Entering declarations does not change the HOL memory domain. -/
theorem enterCountedDeclListHOL_memaddrs {σ : Type} (declarations : List (VarName × BitVec 64))
    (source : PanSemStateFiniteExact 64 σ) :
    (enterCountedDeclListHOL declarations source).memaddrs = source.memaddrs := by
  induction declarations generalizing source with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨name,value⟩
    simpa [enterCountedDeclListHOL,setVarHOLFinite] using ih (setVarHOLFinite (ofString name) (.val (.word value)) source)

end SteppedFlapjack.PanToCrepSteps
