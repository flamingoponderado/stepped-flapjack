import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2
import SteppedFlapjack.CrepToLoopSteps.SimpFixed

/-! Recover the ordinary Crep/Loop code relation for simplifier-fixed programs. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

/-- If every function in the actual list is fixed by Crep simplification, the
original code table has the compiler-proved relation to the actual Loop output. -/
theorem wholeCrep_fixed_codeRel {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (entry : CrepProgHOL width)
    (nodup : (programs.map Prod.fst).Nodup) (found : holAlookup programs start = some ([],entry))
    (fixed : ∀ name params body, (name,params,body) ∈ programs → crepSimpProgHOL body = body) :
    crepToLoopCodeRelExact
      (mkCtxtExact arch HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL programs) 0)
      (alistToFmapCodeExact programs) (sptFromAList (compileProgHOLExact arch programs)) := by
  have relation := mkCtxtCodeImpCodeRel2Exact arch programs start entry ⟨nodup,found⟩
  have same : (alistToFmapCodeExact programs).map2 (fun entry =>
      match entry with | (_,parameters,program) => (parameters,crepSimpProgHOL program)) =
      alistToFmapCodeExact programs := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [HolFiniteMapExact.lookup_map2]
    cases h : (alistToFmapCodeExact programs).lookup key with
    | none => simp
    | some value =>
      obtain ⟨params,body⟩ := value
      have member : (key,params,body) ∈ programs := by
        rw [alistToFmapCodeExact,HolFiniteMapExact.lookup_updateList] at h
        exact flookup_fupdateList_reverse_mem' programs key (params,body) h
      simp [fixed key params body member]
  change crepToLoopCodeRelExact _ _ _ at relation
  rwa [same] at relation


/-- The same relation holds for the executable function map and empty-argument
context that the whole compiler actually uses for its entry. -/
theorem wholeCrep_fixed_executable_codeRel {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (entry : CrepProgHOL width)
    (nodup : (programs.map Prod.fst).Nodup) (found : holAlookup programs start = some ([],entry))
    (fixed : ∀ name params body, (name,params,body) ∈ programs → crepSimpProgHOL body = body) :
    crepToLoopCodeRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0)
      (alistToFmapCodeExact programs) (sptFromAList (compileProgHOLExact arch programs)) := by
  have funcs : crepToLoopMakeFuncsExactExecutable programs = crepToLoopMakeFuncsExactHOL programs := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    exact crepToLoopMakeFuncsExactExecutable_lookup_eq_HOL programs key
  have vars : makeVmapExact [] = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp [makeVmapExact,HolFiniteMapExact.lookup_updateListEq]
  rw [funcs,vars]
  exact wholeCrep_fixed_codeRel arch programs start entry nodup found fixed


/-- Functions covered by the proved branch, tail-entry, and loop fragments. -/
inductive SupportedCodeBody {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | branch {p} : BranchProgram p → SupportedCodeBody p
  | tail {init} : BranchProgram init → (name : MlString) → SupportedCodeBody (.seq init (.call none name []))
  | loop {init condition body tail} : BranchProgram init → BranchCondition condition →
      BranchProgram body → BranchProgram tail → SupportedCodeBody (.seq init (.seq (.while condition body) tail))

/-- Every supported body is a fixed point of the real Crep simplifier. -/
theorem supportedCodeBody_simp_fixed {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : SupportedCodeBody p) : crepSimpProgHOL p = p := by
  cases shape with
  | branch h => exact branchProgram_simp_fixed h
  | tail h name => simp [crepSimpProgHOL,branchProgram_simp_fixed h]
  | loop hi hc hb ht => exact branchConditionWhileBranch_simp_fixed _ hi _ hc _ _ hb ht

/-- Supported syntax discharges the simplifier fixed-point condition for the
actual executable Crep-to-Loop code relation. -/
theorem wholeCrep_supported_executable_codeRel {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (entry : CrepProgHOL width)
    (nodup : (programs.map Prod.fst).Nodup) (found : holAlookup programs start = some ([],entry))
    (shapes : ∀ name params body, (name,params,body) ∈ programs → SupportedCodeBody body) :
    crepToLoopCodeRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0)
      (alistToFmapCodeExact programs) (sptFromAList (compileProgHOLExact arch programs)) := by
  apply wholeCrep_fixed_executable_codeRel arch programs start entry nodup found
  intro name params body member
  exact supportedCodeBody_simp_fixed (shapes name params body member)

end SteppedFlapjack.CrepToLoopSteps
