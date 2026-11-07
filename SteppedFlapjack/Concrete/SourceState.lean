import SteppedFlapjack.Concrete.Fragment
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi
import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory

/-! Fixed source memory and matching single-function environments. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

/- Layout parameters mirror init-e at commit
`254b0d1590010583b727ba5af77d4d706973defb` (InitE/Parameters.lean). -/
def sourceBase : Nat := 0xa1000000
def ramStart : Nat := 0xa0000000
def ramSize : Nat := 29 * 1024 * 1024 * 1024
def ramEnd : Nat := ramStart + ramSize
def stackSize : Nat := 16 * 1024 * 1024
def stackStart : Nat := ramEnd - stackSize
def globalsWords : Nat := 67
def heapEnd : Nat := stackStart - globalsWords * 8
def inputStart : Nat := 0x40000000
def inputSize : Nat := 0x40000000
def inputEnd : Nat := inputStart + inputSize
def outputStart : Nat := 0xa0410000
def outputSize : Nat := 0x1000
def outputEnd : Nat := outputStart + outputSize

def heapBase : BitVec 64 := BitVec.ofNat 64 sourceBase
def heapTop : BitVec 64 := BitVec.ofNat 64 heapEnd

def ordinaryAddress (a : BitVec 64) : Prop :=
  sourceBase ≤ a.toNat ∧ a.toNat < heapEnd ∧ a.toNat % 8 = 0

def sharedAddress (a : BitVec 64) : Prop :=
  a.toNat % 8 = 0 ∧
    ((inputStart ≤ a.toNat ∧ a.toNat < inputEnd) ∨
      (outputStart ≤ a.toNat ∧ a.toNat < outputEnd))

instance (a : BitVec 64) : Decidable (ordinaryAddress a) := by
  unfold ordinaryAddress
  infer_instance

instance (a : BitVec 64) : Decidable (sharedAddress a) := by
  unfold sharedAddress
  infer_instance

/-- The input and output ranges use the same aligned shared-word domain as init-e. -/
theorem sharedAddress_alignment (a : BitVec 64) :
    sharedAddress a ↔ Flapjack.holByteAligned a = true ∧
      ((inputStart ≤ a.toNat ∧ a.toNat < inputEnd) ∨
        (outputStart ≤ a.toNat ∧ a.toNat < outputEnd)) := by
  rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]
  rfl

/-- The interval presentation agrees with the compiler's word-address domain. -/
theorem ordinaryAddress_eq_addresses (a : BitVec 64) :
    ordinaryAddress a ↔ Flapjack.Compiler.Backend.StackRemove.addresses heapBase ((stackStart - sourceBase) / 8 - globalsWords) a := by
  rw [Flapjack.Compiler.Backend.StackRemove.mem_addresses]
  constructor
  · intro h
    refine ⟨(a.toNat - sourceBase) / 8, ?_, ?_⟩
    · simp only [ordinaryAddress,sourceBase,heapEnd,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords] at h
      simp [stackStart,ramEnd,ramStart,ramSize,stackSize,sourceBase,globalsWords]
      omega
    · apply BitVec.eq_of_toNat_eq
      change a.toNat = (BitVec.ofNat 64 sourceBase +
        BitVec.ofNat 64 ((a.toNat - sourceBase) / 8) * BitVec.ofNat 64 8).toNat
      rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
      simp only [ordinaryAddress,sourceBase,heapEnd,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords] at h
      simp only [sourceBase]
      omega
  · rintro ⟨i, hi, h⟩
    simp only [stackStart,ramEnd,ramStart,ramSize,stackSize,sourceBase,globalsWords] at hi
    change a = BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i * BitVec.ofNat 64 8 at h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat] at hn
    simp only [ordinaryAddress,sourceBase,heapEnd,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords]
    simp only [sourceBase] at hn
    omega

/-- The challenge's five startup pointer words; the rest of ordinary memory is zero. -/
def startupHeaders : List (BitVec 64) :=
  [0xa0020018, 0xa0028ff0, 0xa0028ff0, 0x800f0134, 0x800f1000]

def initialWord (a : BitVec 64) : BitVec 64 :=
  if sourceBase ≤ a.toNat ∧ a.toNat < sourceBase + 40 then
    startupHeaders[(a.toNat - sourceBase) / 8]?.getD 0
  else 0

/-- The first and last reserved words match init-e's startup metadata. -/
theorem startup_first_and_last :
    initialWord heapBase = 0xa0020018 ∧ initialWord (heapBase + 32) = 0x800f1000 := by
  decide

/-- This oracle is sufficient for the FFI-free witnesses; it is not init-e's host oracle. -/
def sourceFfi : HolFfiState Unit :=
  { oracle := fun _ s _ bytes => .ret s bytes, ffiState := (), ioEvents := [] }

def sourceTemplate : PanSemStateFiniteExact 64 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  structs := []
  code := HolFiniteMapExact.empty
  eshapes := HolFiniteMapExact.empty
  memory := fun a => .word (initialWord a)
  memaddrs := ordinaryAddress
  shMemaddrs := sharedAddress
  clock := 2^64
  be := false
  ffi := sourceFfi
  baseAddr := heapBase
  topAddr := heapTop

def sourceProduction : PanSemState (RiscV.Word 64) (FfiState Unit) where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := []
  exceptionShapes := fun _ => none
  memory := fun a => some (.word (initialWord a))
  memaddrs := fun a => decide (ordinaryAddress a)
  sharedMemaddrs := fun a => decide (sharedAddress a)
  clock := 2^64
  be := false
  ffi := sourceFfiState sourceFfi
  baseAddress := heapBase
  topAddress := heapTop

/-- The globals pass chooses this entry name for the single-function program. -/
def entryName (body : ProgHOL 64) : MlString :=
  newMainNameHOL (singleEntryProgram (ofString "main") body)

/-- The same fixed source state with a single parameter-free function in its code table. -/
def exactState (body : ProgHOL 64) : PanSemStateFiniteExact 64 Unit :=
  singleEntrySourceTemplate sourceTemplate (entryName body) body

def executableState (body : ProgHOL 64) : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  singleEntrySourceProduction sourceProduction (entryName body) body

instance (body : ProgHOL 64) : DecidablePred (exactState body).memaddrs := by
  change DecidablePred ordinaryAddress
  unfold ordinaryAddress
  infer_instance

theorem source_environment (body : ProgHOL 64) : PanSemEnvironmentRel (executableState body) (exactState body) :=
  singleEntrySource_environment _ _ _ _

theorem source_ranged (body : ProgHOL 64) : PanSemStateRelExecRanged (executableState body) :=
  singleEntrySource_ranged _ _ _

theorem source_related (body : ProgHOL 64) :
    PanSemStateRelExec (executableState body) (exactState body).toExact := by
  have env := source_environment body
  refine ⟨env.1,env.2.1,env.2.2.1,env.2.2.2.1,env.2.2.2.2,?_,?_,?_,rfl,rfl,sourceFfiState_rel _,rfl,rfl⟩
  · intro address present
    rfl
  · intro address
    simp [executableState,exactState,singleEntrySourceProduction,singleEntrySourceTemplate,sourceProduction,sourceTemplate]
  · intro address
    simp [executableState,exactState,singleEntrySourceProduction,singleEntrySourceTemplate,sourceProduction,sourceTemplate]

theorem source_code (body : ProgHOL 64) :
    (exactState body).code.lookup (entryName body) = some ([],body,.one) := by
  simp [exactState,singleEntrySourceTemplate,HolFiniteMapExact.lookup_update,FUPDATE]

end SteppedFlapjack.Concrete
