import SteppedFlapjack.Concrete.FrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps Flapjack.Basis.Pure.MlString

def programWeight : Prog (RiscV.Word 64) → Nat
  | .dec _ _ _ body => 1 + programWeight body
  | .seq a b => 1 + programWeight a + programWeight b
  | .ite _ a b => 1 + programWeight a + programWeight b
  | .while _ body => 1 + programWeight body
  | _ => 1

def holWeight {width : Nat} [NeZero width] : ProgHOL width → Nat
  | .dec _ _ _ body => 1 + holWeight body
  | .seq a b => 1 + holWeight a + holWeight b
  | .ite _ a b => 1 + holWeight a + holWeight b
  | .while _ body => 1 + holWeight body
  | _ => 1

end SteppedFlapjack.Concrete
