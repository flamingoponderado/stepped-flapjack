import Flapjack.Compiler.Backend.RegAlloc.ProductionColourLookup

/-! A list-decoder form of the proved production allocator initializer. -/
namespace SteppedFlapjack.RegAllocSteps
open Flapjack Flapjack.RegAlloc Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc

/-- The hash-indexed decoder is extensionally the original list decoder. -/
theorem indexedDecoder_eq_list (entries : NatInfoMap Nat) :
    cakeSpDefaultIndexed (cakeSpDefaultIndex entries) = CakeAlloc.spDefault entries := by
  funext name
  exact spDefaultIndexed_corresponds entries name

/-- Allocator tags using the direct list decoder. -/
def listDecoderTags (n : Nat) (entries : NatInfoMap Nat) (fs : List Nat) : CakeNodeMap CakeNodeTag :=
  let stackOnly := natSetOfList fs
  (List.range n).foldl (fun tags i =>
    let v := CakeAlloc.spDefault entries i
    match v % 4 with
    | 1 => tags.set i (if stackOnly.contains v then .sTemp else .aTemp)
    | 3 => tags.set i .sTemp
    | _ => tags.set i (.fixed (v / 2))) (CakeNodeMap.ofSize n)

/-- Direct lookup gives exactly the tags produced by the production initializer. -/
theorem listDecoderTags_eq (n : Nat) (entries : NatInfoMap Nat) (fs : List Nat) :
    listDecoderTags n entries fs = cakeMkTags n entries fs := by
  simp only [listDecoderTags,cakeMkTags,spDefaultIndexed_corresponds]
  rfl

/-- The actual allocator initialization expressed with association-list lookup. -/
def listDecoderInit (bij : CakeNodeBijection) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat) : CakeRaState :=
  let ta := CakeAlloc.spDefault bij.toAllocator
  let (adj,_) := cakeMkGraphSet ta tree [] (cakeAdjSetMapOfSize bij.nextNode)
  let adjSets := cakeExtendGraphSet ta forced adj
  let adj := adjSets.mapValues cakeAdjSetList
  let tags := listDecoderTags bij.nextNode bij.fromAllocator fs
  { (CakeRaState.empty bij.nextNode) with
    adjLists := adj, adjSets := some adjSets, nodeTag := tags,
    degrees := CakeNodeMap.filled bij.nextNode 0,
    coalesced := CakeNodeMap.filled bij.nextNode 0,
    moveRelated := CakeNodeMap.filled bij.nextNode false }

/-- Changing only the lookup implementation preserves the entire initial
allocator state, including adjacency, tags, and all auxiliary arrays. -/
theorem listDecoderInit_eq (bij : CakeNodeBijection) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat) :
    listDecoderInit bij tree forced fs = cakeInitRaStateFromBij bij tree forced fs := by
  simp only [listDecoderInit,cakeInitRaStateFromBij, indexedDecoder_eq_list, listDecoderTags_eq]

/-- The move decoder uses the same association-list lookup. -/
theorem allocatorDecoder_eq_list (entries : NatInfoMap Nat) :
    cakeAllocatorIndexLookup (cakeAllocatorIndex entries) = CakeAlloc.spDefault entries := by
  exact indexedDecoder_eq_list entries

/-- Coloring from an initialized state, with direct lookup for source names. -/
def listDecoderColorFromState (alg : CakeAlgorithm) (cost : Option (CakeNodeMap Nat))
    (k : Nat) (moves : List (Nat × (Nat × Nat)))
    (bij : CakeNodeBijection) (state : CakeRaState) : Option (NatInfoMap Nat) :=
  let moves0 := moves.map (cakeUpdateMove (CakeAlloc.spDefault bij.toAllocator))
  let admitted := filterReversed (fun m => cakeFullConsistencyOk state k m.2.1 m.2.2) moves0
  let selected := match alg with | .simple => [] | .irc => admitted
  let (fuel,initial) := cakeInitAlloc1Heu selected k state
  let allocated := cakeRptDoStep cost k fuel initial
  let preferences := cakeResortMovesSp (cakeMovesToSp moves0 (CakeNodeMap.ofSize bij.nextNode))
  let colored := cakeAssignAtemps k allocated.stack (fun s n ks => cakeBiasedPref s preferences n ks) allocated
  let colored := cakeAssignStemps k (fun s n bads => cakeNegBiasedPref s k preferences n bads) colored
  if colored.failure.isSome then none else some (cakeExtractColor colored bij.toAllocator)

/-- Direct source-name lookup preserves the complete production coloring result. -/
theorem listDecoderColorFromState_eq (alg : CakeAlgorithm) (cost : Option (CakeNodeMap Nat))
    (k : Nat) (moves : List (Nat × (Nat × Nat))) (bij : CakeNodeBijection) (state : CakeRaState) :
    listDecoderColorFromState alg cost k moves bij state =
      cakeDoRegAllocFromState alg cost k moves bij state := by
  simp only [listDecoderColorFromState,cakeDoRegAllocFromState,allocatorDecoder_eq_list]
  rfl

/-- Complete production graph allocator with direct list decoders. -/
def listDecoderColor (alg : CakeAlgorithm) (cost : Option (CakeNodeMap Nat))
    (k : Nat) (moves : List (Nat × (Nat × Nat))) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat) : Option (NatInfoMap Nat) :=
  let bij := cakeMkBij tree
  let state := listDecoderInit bij tree forced fs
  listDecoderColorFromState alg cost k moves bij state

/-- The list-decoder variant is exactly the real production graph allocator. -/
theorem listDecoderColor_eq (alg : CakeAlgorithm) (cost : Option (CakeNodeMap Nat))
    (k : Nat) (moves : List (Nat × (Nat × Nat))) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat) :
    listDecoderColor alg cost k moves tree forced fs = cakeDoRegAlloc alg cost k moves tree forced fs := by
  simp only [listDecoderColor,cakeDoRegAlloc,listDecoderInit_eq,listDecoderColorFromState_eq]

end SteppedFlapjack.RegAllocSteps
