import SteppedFlapjack.Concrete.CountedScalar
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

/-- Call-free source programs have the same counted run under any call contracts. -/
theorem supported_counted_contract_irrel {σ : Type}
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (structs : StructContext) (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (base top : BitVec 64) (access : Option (PanValueMemoryAccess (RiscV.Word 64))) (fuel : Nat) :
    ∀ {scope program}, SupportedIn scope program → ∀ locals globals memory ffi
      (c₁ c₂ : Option PanValueCallContracts),
      evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
        locals globals memory ffi program (memoryAccess := access) (contracts := c₁) =
      evalPanValueFfiProgSteps context primitive handler structs functions base top panSemBitVec64BytesInWord fuel
        locals globals memory ffi program (memoryAccess := access) (contracts := c₂) := by
  induction fuel with
  | zero => intros; simp [evalPanValueFfiProgSteps]
  | succ fuel ih =>
    intro scope program shape locals globals memory ffi c₁ c₂
    cases shape with
    | skip => simp [evalPanValueFfiProgSteps]
    | assign name member scalar => simp [evalPanValueFfiProgSteps]
    | ret scalar => simp [evalPanValueFfiProgSteps]
    | decl name scalar bodyShape => simp only [evalPanValueFfiProgSteps,ih bodyShape _ _ _ _ c₁ c₂]
    | seq aShape bShape => simp only [evalPanValueFfiProgSteps,ih aShape _ _ _ _ c₁ c₂,ih bShape _ _ _ _ c₁ c₂]
    | ite scalar aShape bShape => simp only [evalPanValueFfiProgSteps,ih aShape _ _ _ _ c₁ c₂,ih bShape _ _ _ _ c₁ c₂]
    | @«while» scope condition body scalar bodyShape =>
      simp only [evalPanValueFfiProgSteps,ih bodyShape _ _ _ _ c₁ c₂,ih (SupportedIn.while scalar bodyShape) _ _ _ _ c₁ c₂]

end SteppedFlapjack.Concrete
