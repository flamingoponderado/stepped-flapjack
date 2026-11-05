import SteppedFlapjack.PanValueFfiClockFuel
import SteppedFlapjack.Test.PanValueFfiSemantics

/-! Executable regressions for clocked fuel monotonicity: raising the fuel
changes neither the outcome nor the clock.

The three programs are the three shapes the proof distinguishes — a leaf whose
body never mentions the fuel, a `seq` that recurses twice at `fuel`, and a
`while` whose next iteration recurses at `fuel` again. The `while` is the one
worth having: it is where fuel being a *depth* budget rather than a work
budget is easiest to get wrong. -/

namespace Flapjack

open RiscV

def clockFuelWhile : Prog (Word 64) :=
  .while (.const (BitVec.ofNat 64 1)) .tick

def clockFuelSeq : Prog (Word 64) :=
  .seq .tick .tick

/-- Run `program` at `fuel` in the stateful test configuration. -/
def clockFuelRun (fuel clock : Nat) (program : Prog (Word 64)) :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 fuel (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState clock program

/-- Two runs agree on both the outcome shape and the clock. There is no `BEq`
on `PanValueFfiClockResult`, so the comparison is spelled out; the clock is
the half that matters here, since fuel monotonicity has to preserve it
exactly. -/
def clockFuelAgrees (a b : Option (PanValueFfiClockResult (Word 64) Unit)) : Bool :=
  match a, b with
  | some (.control (.normal _ _ _ _), c1), some (.control (.normal _ _ _ _), c2) => c1 == c2
  | some (.timeout _ _ _ _, c1), some (.timeout _ _ _ _, c2) => c1 == c2
  | _, _ => false

-- a leaf: fuel is irrelevant beyond 1
#guard clockFuelAgrees (clockFuelRun 1 3 .tick) (clockFuelRun 40 3 .tick)
-- a `seq`: needs 2, unchanged at 40
#guard clockFuelAgrees (clockFuelRun 2 3 clockFuelSeq) (clockFuelRun 40 3 clockFuelSeq)
-- a `while`: iterates until the clock runs out, unchanged at 40
#guard clockFuelAgrees (clockFuelRun 5 3 clockFuelWhile) (clockFuelRun 40 3 clockFuelWhile)
-- the runs really succeed, so the agreements above are not `none` vs `none`
#guard (clockFuelRun 1 3 (.tick : Prog (Word 64))).isSome
#guard (clockFuelRun 2 3 clockFuelSeq).isSome
#guard (clockFuelRun 5 3 clockFuelWhile).isSome
-- and the clock really is being spent, so the comparison has content
#guard match clockFuelRun 2 3 clockFuelSeq with | some (_, c) => c == 1 | _ => false

/-- The theorem itself, instantiated at the test configuration. -/
example (fuel fuel' clock : Nat) (program : Prog (Word 64))
    (result : PanValueFfiClockResult (Word 64) Unit)
    (hfuel : fuel ≤ fuel')
    (hrun : clockFuelRun fuel clock program = some result) :
    clockFuelRun fuel' clock program = some result :=
  evalPanValueFfiClockProg_fuel_mono statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 _ _ _ statefulTestFfiState clock program
    none none none hfuel hrun

end Flapjack
