import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.PrimitiveProductionBridge
import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Flapjack.Pancake.WordLang
import SteppedFlapjack.PanValueExpCounted

/-!
Counted field evaluation against the states of `Flapjack.Test.PanSemStateEvalParity`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanSemStateEvalParity

open Flapjack

private abbrev Word64 := RiscV.Word 64

def sourceMemoryWord : Word64 := BitVec.ofNat 64 0x1122334455667788

def sourceState (bigEndian inWordDomain inSharedDomain : Bool) :
    PanSemState Word64 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun address =>
      if address == 0 then some (.word sourceMemoryWord) else none
    memaddrs := fun _ => inWordDomain
    sharedMemaddrs := fun _ => inSharedDomain
    clock := 0
    be := bigEndian
    ffi := ()
    baseAddress := 0
    topAddress := 0 }

def littleEndianState : PanSemState Word64 Unit := sourceState false true true

def bigEndianState : PanSemState Word64 Unit := sourceState true true true

/- Counted field expressions must use the caller's state-owned access, just as
   counted expressions and argument lists do. -/
private def countedByteField (state : PanSemState Word64 Unit) :=
  evalPanValueFieldsCountedWithAccess state.structs state.locals state.globals state.memory
    state.baseAddress state.topAddress panSemBitVec64BytesInWord
    [("byte", .loadByte (.const 0))]
    (memoryAccess := some (panSemBitVec64MemoryAccess state))

#guard (countedByteField littleEndianState).map (fun result =>
  match result.1 with
  | [("byte", .word value)] => value == (0x88 : Word64)
  | _ => false) == some true

#guard (countedByteField bigEndianState).map (fun result =>
  match result.1 with
  | [("byte", .word value)] => value == (0x11 : Word64)
  | _ => false) == some true

#guard (countedByteField (sourceState false false true)).isNone

end Flapjack.Test.PanSemStateEvalParity
