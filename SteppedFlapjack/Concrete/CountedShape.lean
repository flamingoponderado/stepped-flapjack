import SteppedFlapjack.Concrete.CountedScalar
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

def BasicControl {σ : Type} : PanValueFfiControlResult (RiscV.Word 64) σ → Prop
  | .normal _ _ _ _ | .error _ _ _ _ => True
  | .returned _ _ _ _ values => values.length = 1
  | _ => False

private theorem basic_restore {σ : Type} (name : VarName) (old : Option (PanValue (RiscV.Word 64)))
    (result : PanValueFfiControlResult (RiscV.Word 64) σ) (basic : BasicControl result) :
    BasicControl (restorePanValueFfiLocal name old result) := by
  cases result <;> simp_all [BasicControl,restorePanValueFfiLocal]

theorem supported_counted_basic {σ : Type}
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (base top : BitVec 64) (access : Option (PanValueMemoryAccess (RiscV.Word 64))) (fuel : Nat) :
    ∀ {scope program}, SupportedIn scope program → ∀ locals globals memory ffi result count,
      evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
        locals globals memory ffi program (memoryAccess := access) = some (result,count) → BasicControl result := by
  induction fuel with
  | zero => intro scope program shape locals globals memory ffi result count run; simp [evalPanValueFfiProgSteps] at run
  | succ fuel ih =>
    intro scope program shape locals globals memory ffi result count run
    cases shape with
    | skip =>
      simp [evalPanValueFfiProgSteps] at run
      obtain ⟨rfl,rfl⟩ := run
      trivial
    | @assign scope name expression member scalar =>
      simp only [evalPanValueFfiProgSteps,panValueAssignLocalResult] at run
      cases evaluated : evalPanValueExpCounted structs locals globals memory base top panSemBitVec64BytesInWord
          expression access with
      | none =>
        simp only [evaluated,Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,_⟩ := run
        trivial
      | some pair =>
        rcases pair with ⟨value,cost⟩
        simp only [evaluated] at run
        split at run <;> simp only [Option.some.injEq,Prod.mk.injEq] at run <;>
          obtain ⟨rfl,_⟩ := run <;> trivial
    | @ret scope expression scalar =>
      simp only [evalPanValueFfiProgSteps,panValueReturnResult] at run
      cases evaluated : evalPanValueExpCounted structs locals globals memory base top panSemBitVec64BytesInWord
          expression access with
      | none =>
        simp only [evaluated,Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,_⟩ := run
        trivial
      | some pair =>
        rcases pair with ⟨value,cost⟩
        simp only [evaluated] at run
        split at run <;> simp only [Option.some.injEq,Prod.mk.injEq] at run <;>
          obtain ⟨rfl,_⟩ := run <;> simp [BasicControl]
    | @decl scope name expression body scalar bodyShape =>
      simp only [evalPanValueFfiProgSteps] at run
      cases accepted : panValueDecAccepted structs base top panSemBitVec64BytesInWord locals globals memory expression access .one with
      | none =>
        simp only [accepted,Option.elim_none,Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,_⟩ := run
        trivial
      | some pair =>
        rcases pair with ⟨value,cost⟩
        cases bodyRun : evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
            (updatePanValueMap locals name value) globals memory ffi body (memoryAccess := access) with
        | none => simp [accepted,bodyRun] at run
        | some outcome =>
          rcases outcome with ⟨bodyResult,bodyCost⟩
          simp only [accepted,Option.elim_some,bodyRun] at run
          obtain ⟨rfl,_⟩ := run
          exact basic_restore name (locals name) bodyResult (ih bodyShape _ _ _ _ _ _ bodyRun)
    | @seq scope a b aShape bShape =>
      simp only [evalPanValueFfiProgSteps] at run
      cases firstRun : evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
          locals globals memory ffi a (memoryAccess := access) with
      | none => simp [firstRun] at run
      | some outcome =>
        rcases outcome with ⟨firstResult,firstCost⟩
        have firstBasic := ih aShape locals globals memory ffi firstResult firstCost firstRun
        cases firstResult with
        | normal nextLocals nextGlobals nextMemory nextFfi =>
          cases secondRun : evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
              nextLocals nextGlobals nextMemory nextFfi b (memoryAccess := access) with
          | none => simp [firstRun,secondRun] at run
          | some second =>
            rcases second with ⟨secondResult,secondCost⟩
            simp [firstRun,secondRun] at run
            obtain ⟨rfl,_⟩ := run
            exact ih bShape nextLocals nextGlobals nextMemory nextFfi secondResult secondCost secondRun
        | error l g m f =>
          simp [firstRun] at run
          obtain ⟨rfl,_⟩ := run
          exact firstBasic
        | returned l g m f values =>
          simp [firstRun] at run
          obtain ⟨rfl,_⟩ := run
          exact firstBasic
        | raised l g m f e v => exact False.elim firstBasic
        | broke l g m f => exact False.elim firstBasic
        | continued l g m f => exact False.elim firstBasic
        | finalFfi l g m f e => exact False.elim firstBasic
    | @ite scope condition a b scalar aShape bShape =>
      simp only [evalPanValueFfiProgSteps] at run
      cases condRun : panValueIteCondition structs base top panSemBitVec64BytesInWord locals globals memory condition access with
      | none =>
        simp [condRun] at run
        obtain ⟨rfl,_⟩ := run
        trivial
      | some pair =>
        rcases pair with ⟨word,cost⟩
        by_cases zero : word = 0
        · cases branchRun : evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
              locals globals memory ffi b (memoryAccess := access) with
          | none => simp [condRun,zero,branchRun] at run
          | some outcome =>
            rcases outcome with ⟨branchResult,branchCost⟩
            simp [condRun,zero,branchRun] at run
            obtain ⟨rfl,_⟩ := run
            exact ih bShape locals globals memory ffi branchResult branchCost branchRun
        · have zeroBits : word ≠ (0#64) := by simpa using zero
          cases branchRun : evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
              locals globals memory ffi a (memoryAccess := access) with
          | none => simp [condRun,zeroBits,branchRun] at run
          | some outcome =>
            rcases outcome with ⟨branchResult,branchCost⟩
            simp [condRun,zeroBits,branchRun] at run
            obtain ⟨rfl,_⟩ := run
            exact ih aShape locals globals memory ffi branchResult branchCost branchRun
    | @«while» scope condition body scalar bodyShape =>
      simp only [evalPanValueFfiProgSteps] at run
      cases condRun : panValueIteCondition structs base top panSemBitVec64BytesInWord locals globals memory condition access with
      | none =>
        simp [condRun] at run
        obtain ⟨rfl,_⟩ := run
        trivial
      | some pair =>
        rcases pair with ⟨word,cost⟩
        by_cases zero : word = 0
        · simp [condRun,zero] at run
          obtain ⟨rfl,_⟩ := run
          trivial
        · have zeroBits : word ≠ (0#64) := by simpa using zero
          cases bodyRun : evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
              locals globals memory ffi body (memoryAccess := access) with
          | none => simp [condRun,zeroBits,bodyRun] at run
          | some outcome =>
            rcases outcome with ⟨bodyResult,bodyCost⟩
            have bodyBasic := ih bodyShape locals globals memory ffi bodyResult bodyCost bodyRun
            cases bodyResult with
            | normal nextLocals nextGlobals nextMemory nextFfi =>
              cases restRun : evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
                  nextLocals nextGlobals nextMemory nextFfi (.while condition body) (memoryAccess := access) with
              | none => simp [condRun,zeroBits,bodyRun,restRun] at run
              | some rest =>
                rcases rest with ⟨restResult,restCost⟩
                simp [condRun,zeroBits,bodyRun,restRun] at run
                obtain ⟨rfl,_⟩ := run
                exact ih (SupportedIn.while scalar bodyShape) nextLocals nextGlobals nextMemory nextFfi restResult restCost restRun
            | error l g m f =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,_⟩ := run
              exact bodyBasic
            | returned l g m f values =>
              simp [condRun,zeroBits,bodyRun] at run
              obtain ⟨rfl,_⟩ := run
              exact bodyBasic
            | raised l g m f e v => exact False.elim bodyBasic
            | broke l g m f => exact False.elim bodyBasic
            | continued l g m f => exact False.elim bodyBasic
            | finalFfi l g m f e => exact False.elim bodyBasic
end SteppedFlapjack.Concrete
