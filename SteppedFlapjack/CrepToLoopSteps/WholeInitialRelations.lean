import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.LoopToWordSteps.WholeCodeRel
import SteppedFlapjack.WordAllocSteps.WholeFrontendShapes
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization

/-! Initialize frontend code relations from actual whole-program outputs. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

/-- The data portion of the Loop/Word relation, without any code-table
hypothesis. It retains the heap and global-state conditions of the semantics. -/
def LoopWordDataRel {width : Nat} [NeZero width] {C F : Type}
    (loop : LoopSemStateFiniteExact width F) (word : WordSemStateFiniteExact width C F) : Prop :=
  ∃ len : BitVec width,
    word.memory = loop.memory ∧ word.mdomain = loop.mdomain ∧ word.shMdomain = loop.shMdomain ∧
    word.clock = loop.clock ∧ word.be = loop.be ∧ word.ffi = loop.ffi ∧
    word.store.lookup .currHeap = some (.word loop.baseAddr) ∧
    word.store.lookup .heapLength = some (.word len) ∧
    loop.topAddr = loop.baseAddr + (2 : BitVec width) * len ∧
    loopToWordGlobalsRelHOLExact loop.globals word.store

/-- The actual native Word entry has exactly the data relation induced by the
initial Stack state. Entry locals, the generated code table and frame size do
not affect the shared data relation. -/
theorem nativeEntry_loopWordDataRel_iff {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frameSize : Nat)
    (stack : StackSemStateFiniteExact width C F)
    (compiledCode originalCode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (loop : LoopSemStateFiniteExact width F) :
    LoopWordDataRel loop
      {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW width)] (some frameSize)
        (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k stack compiledCode coracle) with
          code := originalCode} ↔
    ∃ len : BitVec width,
      stack.memory = loop.memory ∧ stack.mdomain = loop.mdomain ∧ stack.shMdomain = loop.shMdomain ∧
      stack.clock = loop.clock ∧ stack.be = loop.be ∧ stack.ffi = loop.ffi ∧
      stack.store.lookup .currHeap = some (.word loop.baseAddr) ∧
      stack.store.lookup .heapLength = some (.word len) ∧
      loop.topAddr = loop.baseAddr + (2 : BitVec width) * len ∧
      loopToWordGlobalsRelHOLExact loop.globals stack.store := by
  simp [LoopWordDataRel, WordSemStateFiniteExact.callEnv,
    Compiler.Backend.WordToStack.Native.Initialization.makeInit, loopToWordGlobalsRelHOLExact,
    HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]

/-- Initial data relations and supported whole-program syntax give both full
frontend state/code relations for the actual compiled code tables. -/
theorem wholeFrontend_initial_relations {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (entry : CrepProgHOL width)
    (nodup : (programs.map Prod.fst).Nodup) (found : holAlookup programs start = some ([],entry))
    (shapes : ∀ name params body, (name,params,body) ∈ programs → SupportedCodeBody body)
    (source : CrepSemHOLState width F) (loop : LoopSemStateFiniteExact width F)
    (word : WordSemStateFiniteExact width C F)
    (state : crepToLoopStateRelExact source loop)
    (memory : crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs)
    (globals : crepToLoopGlobalsRelHOLExact source.globals loop.globals)
    (locals : crepToLoopLocalsRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0)
      .ln source.locals loop.locals)
    (data : LoopWordDataRel loop word) :
    let source := {source with code := alistToFmapCodeExact programs}
    let loop := {loop with code := sptFromAList (compileProgHOLExact arch programs)}
    let word := {word with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch programs))}
    crepToLoopStateRelExact source loop ∧
    crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs ∧
    crepToLoopGlobalsRelHOLExact source.globals loop.globals ∧
    crepToLoopLocalsRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0)
      .ln source.locals loop.locals ∧
    crepToLoopCodeRelExact
      (mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0)
      source.code loop.code ∧
    loopToWordStateRelHOLExact loop word ∧
    WordAllocSteps.TailProgramShapes (loopToWordCompileHOL (compileProgHOLExact arch programs)) := by
  obtain ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals⟩ := data
  exact ⟨state,memory,globals,locals,wholeCrep_supported_executable_codeRel arch programs start entry nodup found shapes,
    ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals,LoopToWordSteps.wholeCrepLoopWord_codeRel arch programs⟩,
    WordAllocSteps.wholeCrep_word_shapes arch programs shapes⟩

end SteppedFlapjack.CrepToLoopSteps
