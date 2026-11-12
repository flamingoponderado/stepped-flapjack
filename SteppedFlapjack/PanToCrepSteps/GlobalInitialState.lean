import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsCons
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Backend.StackRemove Flapjack.Basis.Pure.MlString

def beforeGlobals {width : Nat} {σ : Type} [NeZero width]
    (target : PanSemStateFiniteExact width σ) (size : BitVec width) (words : Nat) : PanSemStateFiniteExact width σ :=
  { target with
    topAddr := target.topAddr - size
    memaddrs := fun a => target.memaddrs a ∧ ¬ addresses (target.topAddr - size) words a
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    structs := [] }

def beforeGlobalsContext {width : Nat} [NeZero width] (size : BitVec width) : PanGlobalsContextExact width :=
  { globals := HolFiniteMapExact.empty, globalsSize := 0, maxGlobalsSize := size }

private theorem beforeGlobals_related {width : Nat} {σ : Type} [NeZero width]
    (target : PanSemStateFiniteExact width σ) (size : BitVec width) (words : Nat)
    (structs : target.structs = []) (topFree : ¬ target.memaddrs target.topAddr)
    (aligned : panGlobalsByteAlignedHOL target.topAddr) (widthOK : goodDimindex width) :
    panGlobalsStateRelHOLExact false (beforeGlobalsContext size) (beforeGlobals target size words) target := by
  simp [panGlobalsStateRelHOLExact, beforeGlobals, beforeGlobalsContext, structs, topFree, aligned, widthOK,
    disjointGlobalsHOLExact, HolFiniteMapExact.lookup_empty]
  intro address present _
  exact present

/-- Construct and simulate the initial global declarations in the reserved target range. -/
private theorem beforeGlobals_initializers {width : Nat} {σ : Type} [NeZero width]
    (target : PanSemStateFiniteExact width σ) (decs : List (DeclHOL width))
    (post : PanSemStateFiniteExact width σ) (initializers : List (ProgHOL width))
    (funs exns : List (DeclHOL width)) (context : PanGlobalsContextExact width)
    (structs : target.structs = []) (topFree : ¬ target.memaddrs target.topAddr)
    (aligned : panGlobalsByteAlignedHOL target.topAddr) (widthOK : goodDimindex width)
    (onlyDecls : ∀ d ∈ decs, isDeclHOL d = true)
    (eval : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      (beforeGlobals target (panBytesInWord width * BitVec.ofNat width ((decShapesHOL decs).map sizeOfShapeHOL).sum)
        ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      (fun _a => Classical.propDecidable _) decs = some post)
    (compiled : compileDecsExactHOL
      (beforeGlobalsContext (panBytesInWord width * BitVec.ofNat width ((decShapesHOL decs).map sizeOfShapeHOL).sum)) decs =
        (initializers,funs,exns,context))
    (allocated : ∀ a, addresses (target.topAddr - panBytesInWord width *
      BitVec.ofNat width ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      ((decShapesHOL decs).map sizeOfShapeHOL).sum a → target.memaddrs a)
    (sizeBound : (panBytesInWord width).toNat * ((decShapesHOL decs).map sizeOfShapeHOL).sum < 2 ^ width) :
    ∃ final, PanSemStateFiniteExact.evaluateHOLFiniteState target (nestedSeqHOL initializers) = (none,final) ∧
      panGlobalsStateRelHOLExact false context post final ∧
      final.clock = target.clock ∧ final.ffi = target.ffi ∧ final.locals = target.locals ∧
      panGlobalsByteAlignedHOL context.globalsSize := by
  classical
  let words := ((decShapesHOL decs).map sizeOfShapeHOL).sum
  let size := panBytesInWord width * BitVec.ofNat width words
  let source := beforeGlobals target size words
  let free := addresses (target.topAddr - size) words
  apply PanGlobalsInitGlobalsAssembly.initGlobalsAll source decs (beforeGlobalsContext size)
    post initializers funs exns context target free
  refine ⟨eval,onlyDecls,compiled,beforeGlobals_related target size words structs topFree aligned widthOK,?_,?_,?_,?_,?_,?_,sizeBound⟩
  · simp [free,size,words,beforeGlobalsContext]
  · intro a hsource hfree
    exact hsource.2 hfree
  · exact allocated
  · simp [beforeGlobalsContext,panGlobalsByteAlignedHOL,panByteAlignHOL]
  · rfl
  · intro v sh addr h
    simp [source,beforeGlobals,HolFiniteMapExact.lookup_empty] at h

def installSourceFunctions {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) : PanSemStateFiniteExact width σ :=
  { state with
    locals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty.updateList entries.reverse }

def installTargetFunctions {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (ctx : PanGlobalsContextExact width)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) : PanSemStateFiniteExact width σ :=
  { state with
    locals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty.updateList (entries.map (fun e => (e.1,e.2.1,compileProgExactHOL ctx e.2.2.1,e.2.2.2))).reverse }

private theorem installFunctions_related {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ) (ctx : PanGlobalsContextExact width)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (related : panGlobalsStateRelHOLExact false ctx source target) :
    panGlobalsStateRelHOLExact true ctx (installSourceFunctions source entries) (installTargetFunctions target ctx entries) := by
  simp only [panGlobalsStateRelHOLExact] at related ⊢
  rcases related with ⟨top,_,base,be,eshapes,clock,structs,targetStructs,globals,wf,domain,shared,memory,ffi,_,disjoint,topFree,aligned,widthOK⟩
  refine ⟨top,by intro _; rfl,base,be,eshapes,clock,structs,targetStructs,globals,wf,domain,shared,memory,ffi,?_,disjoint,topFree,aligned,widthOK⟩
  intro name params body shape found
  change FLOOKUP (FUPDATE_LIST FEMPTY (entries.map (fun e => (e.1,e.2.1,compileProgExactHOL ctx e.2.2.1,e.2.2.2))).reverse) name = _
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup,lookup_mapBodies]
  change FLOOKUP (FUPDATE_LIST FEMPTY entries.reverse) name = _ at found
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at found
  simp [found]
/-- Initialize the globals and install the corresponding compiled functions. -/
theorem beforeGlobals_initializedFunctions {width : Nat} {σ : Type} [NeZero width]
    (target : PanSemStateFiniteExact width σ) (decs : List (DeclHOL width))
    (post : PanSemStateFiniteExact width σ) (initializers : List (ProgHOL width))
    (funs exns : List (DeclHOL width)) (context : PanGlobalsContextExact width)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (structs : target.structs = []) (topFree : ¬ target.memaddrs target.topAddr)
    (aligned : panGlobalsByteAlignedHOL target.topAddr) (widthOK : goodDimindex width)
    (onlyDecls : ∀ d ∈ decs, isDeclHOL d = true)
    (eval : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      (beforeGlobals target (panBytesInWord width * BitVec.ofNat width ((decShapesHOL decs).map sizeOfShapeHOL).sum)
        ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      (fun _a => Classical.propDecidable _) decs = some post)
    (compiled : compileDecsExactHOL
      (beforeGlobalsContext (panBytesInWord width * BitVec.ofNat width ((decShapesHOL decs).map sizeOfShapeHOL).sum)) decs =
        (initializers,funs,exns,context))
    (allocated : ∀ a, addresses (target.topAddr - panBytesInWord width *
      BitVec.ofNat width ((decShapesHOL decs).map sizeOfShapeHOL).sum)
      ((decShapesHOL decs).map sizeOfShapeHOL).sum a → target.memaddrs a)
    (sizeBound : (panBytesInWord width).toNat * ((decShapesHOL decs).map sizeOfShapeHOL).sum < 2 ^ width) :
    ∃ final, PanSemStateFiniteExact.evaluateHOLFiniteState target (nestedSeqHOL initializers) = (none,final) ∧
      panGlobalsStateRelHOLExact true context (installSourceFunctions post entries)
        (installTargetFunctions final context entries) ∧
      final.clock = target.clock ∧ final.ffi = target.ffi ∧ final.locals = target.locals ∧
      panGlobalsByteAlignedHOL context.globalsSize := by
  obtain ⟨final,run,rel,clock,ffi,locals,alignment⟩ :=
    beforeGlobals_initializers target decs post initializers funs exns context structs topFree aligned widthOK
      onlyDecls eval compiled allocated sizeBound
  exact ⟨final,run,installFunctions_related post final context entries rel,clock,ffi,locals,alignment⟩

end SteppedFlapjack.PanToCrepSteps
