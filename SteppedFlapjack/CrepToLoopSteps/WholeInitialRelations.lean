import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.LoopToWordSteps.WholeCodeRel
import SteppedFlapjack.WordAllocSteps.WholeFrontendShapes
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization
import SteppedFlapjack.WordToStackSteps.TailEntryFrame

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

/-- Once the Stack data match a Loop state, every frame size yields the same
frontend data relation and the native zero-argument Word entry has the locals
required by Loop-to-Word. This lets the frame be chosen after establishing
the frontend data relation. -/
theorem nativeEntry_frontend_facts {C F : Type}
    (ac : AsmConfigExact 64) (k firstFrame : Nat)
    (stack : StackSemStateFiniteExact 64 C F)
    (compiledCode originalCode : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (loop : LoopSemStateFiniteExact 64 F) (program : HolLoopProg 64)
    (data : LoopWordDataRel loop
      {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some firstFrame)
        (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k stack compiledCode coracle) with
          code := originalCode})
    (gc : Compiler.Backend.WordSimp.gcFunConstOk stack.gcFun) :
    ∀ frameSize,
      let word := {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
        (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k stack compiledCode coracle) with
          code := originalCode}
      let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
        (sptDifference (accVarsHOL program .ln) (LoopToWord.toNumSetHOL []))) .ln
      LoopWordDataRel loop word ∧ word.code = originalCode ∧
      Compiler.Backend.WordSimp.gcFunConstOk word.gcFun ∧
      LoopToWord.localsRelHOL ctxt .ln word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) := by
  have stackData := (nativeEntry_loopWordDataRel_iff ac k firstFrame stack compiledCode originalCode coracle loop).mp data
  intro frameSize
  refine ⟨(nativeEntry_loopWordDataRel_iff ac k frameSize stack compiledCode originalCode coracle loop).mpr stackData,
    rfl,?_,?_,?_⟩
  · exact gc
  · exact (SteppedFlapjack.WordToStackSteps.nativeTailEntry_loopLocals program
      (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k stack compiledCode coracle) frameSize).1
  · exact (SteppedFlapjack.WordToStackSteps.nativeEntry_locals
      (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k stack compiledCode coracle) frameSize 0).2.2

/-- At the zero-argument entry, no Loop variable is live. Replace the Loop
locals by the empty tree without changing any data or state relation; this
aligns the frontend state with the compiler-initialized native Word entry. -/
theorem emptyLive_initial_relations {width : Nat} [NeZero width] {C F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (loop : LoopSemStateFiniteExact width F) (word : WordSemStateFiniteExact width C F)
    (state : crepToLoopStateRelExact source loop)
    (memory : crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs)
    (globals : crepToLoopGlobalsRelHOLExact source.globals loop.globals)
    (locals : crepToLoopLocalsRelExact ctxt .ln source.locals loop.locals)
    (data : LoopWordDataRel loop word) :
    let initial := {loop with locals := .ln}
    crepToLoopStateRelExact source initial ∧
    crepToLoopMemRelHOLExact source.memory initial.memory source.memaddrs ∧
    crepToLoopGlobalsRelHOLExact source.globals initial.globals ∧
    crepToLoopLocalsRelExact ctxt .ln source.locals initial.locals ∧
    LoopWordDataRel initial word := by
  refine ⟨state,memory,globals,?_,data⟩
  refine ⟨locals.1,locals.2.1,?_,?_⟩
  · intro n h
    simp [sptMem, sptDomain] at h
  · intro name value found
    obtain ⟨n,_,live,_⟩ := locals.2.2.2 name value found
    simp [sptMem, sptDomain] at live

end SteppedFlapjack.CrepToLoopSteps
