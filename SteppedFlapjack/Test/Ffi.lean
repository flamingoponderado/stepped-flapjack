import Flapjack.RiscV.Link
import Flapjack.Ffi
import SteppedFlapjack.PanValueFfiSemantics

/-!
The stepped counterpart of the I/O-event prefix lemma checked in `Flapjack.Test.Ffi`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack

#check @evalPanValueFfiProgSteps_extCall_returned_ioEvents_prefix

end Flapjack
