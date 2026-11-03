import Flapjack.Test.PanSemStateEvalParity
import SteppedFlapjack.PanValueExpCounted

/-!
Counted field evaluation against the states of `Flapjack.Test.PanSemStateEvalParity`.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemStateEvalParity

open Flapjack

/- Counted field expressions must use the caller's state-owned access, just as
   counted expressions and argument lists do. -/
private def countedByteField (state : PanSemState Word64 Unit) :=
  evalPanValueFieldsCounted state.structs state.locals state.globals state.memory
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
