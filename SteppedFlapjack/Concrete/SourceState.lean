import SteppedFlapjack.Concrete.Fragment
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi
import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals

/-! Fixed source memory and matching single-function environments. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

/-- The 64 KiB example starts at 65536; its full machine byte domain ends at 196608. -/
def heapBase : BitVec 64 := 65536
def heapTop : BitVec 64 := 196608

def sourceFfi : HolFfiState Unit :=
  { oracle := fun _ s _ bytes => .ret s bytes, ffiState := (), ioEvents := [] }

def sourceTemplate : PanSemStateFiniteExact 64 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  structs := []
  code := HolFiniteMapExact.empty
  eshapes := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun a => 65536 ≤ a.toNat ∧ a.toNat < 196608 ∧ a.toNat % 8 = 0
  shMemaddrs := fun _ => False
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
  memory := fun _ => some (.word 0)
  memaddrs := fun a => decide (65536 ≤ a.toNat ∧ a.toNat < 196608 ∧ a.toNat % 8 = 0)
  sharedMemaddrs := fun _ => false
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
  change DecidablePred (fun a : BitVec 64 => 65536 ≤ a.toNat ∧ a.toNat < 196608 ∧ a.toNat % 8 = 0)
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
