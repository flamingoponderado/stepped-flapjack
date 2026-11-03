import Flapjack.Test.PanValueFfiCore
import SteppedFlapjack.PanValueFfiSemantics

/-!
Executable checks for the stateful stepped source evaluator, on the fixtures of
`Flapjack.Test.PanValueFfiCore`. The oracle returns a fixed word for shared
reads and echoes write payloads, which makes both the `SharedMem` event and the
stepped result observable.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack

open RiscV

def statefulSharedProgram : Option (Word 64 × Nat × Nat) :=
  (evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 30 (fun _ => none) (fun _ => none) (fun _ => none)
      statefulTestFfiState
      (.dec "x" .one (.const (BitVec.ofNat 64 0))
        (.seq (.shMemStore .op8 (.const (BitVec.ofNat 64 9))
            (.const (BitVec.ofNat 64 0xaa)))
          (.seq (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10)))
            (.return (.var .local "x")))))).map
    fun result => match result.1 with
      | .returned _ _ _ ffi [.word value] => (value, result.2, ffi.ioEvents.length)
      | _ => (BitVec.ofNat 64 0, 0, 0)

def statefulSharedFinalResult :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
      statefulTestFinalState
      (.dec "x" .one (.const (BitVec.ofNat 64 0))
        (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10))))

def statefulSharedFinal : Bool :=
  match statefulSharedFinalResult with
  | some (.finalFfi locals _ _ _ event, steps) =>
      locals "x" = none && event.name = .sharedMem .mappedRead &&
        event.outcome = .failed && steps = 4
  | _ => false

#guard statefulSharedProgram = some (BitVec.ofNat 64 0x42, 11, 2)
#guard statefulSharedFinal

def statefulDecCallFinalResult :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler []
      [("finalCallee", [],
        .dec "x" .one (.const (BitVec.ofNat 64 0))
          (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10))))]
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 10
      (fun _ => none) (fun _ => none) statefulTestMemory
      statefulTestFinalState
      (.decCall "x" .one "finalCallee" [] .skip)
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

def statefulDecCallFinal : Bool :=
  match statefulDecCallFinalResult with
  | some (.finalFfi locals _ _ _ event, steps) =>
      locals "x" = none && event.name = .sharedMem .mappedRead &&
        event.outcome = .failed && steps = 5
  | _ => false

#guard statefulDecCallFinal

/- CakeML's final shared-store outcome preserves the current locals, unlike
   the final shared-load and ExtCall boundaries which clear them. -/
def statefulSharedStoreFinalResult :=
  evalPanValueFfiProgSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 10
      (fun name =>
        if name == "x" then some (.word (BitVec.ofNat 64 0)) else none)
      (fun _ => none) (fun _ => none) statefulTestFinalState
      (.shMemStore .op8 (.const (BitVec.ofNat 64 10))
        (.const (BitVec.ofNat 64 0xaa)))

def statefulSharedStoreFinal : Bool :=
  match statefulSharedStoreFinalResult with
  | some (.finalFfi locals _ _ _ event, steps) =>
        (match locals "x" with
       | some (.word value) => value == BitVec.ofNat 64 0
       | _ => false) &&
        event.name == .sharedMem .mappedWrite &&
        event.outcome == .failed && steps == 3
  | _ => false

#guard statefulSharedStoreFinal

#guard
  (match
    evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
      statefulTestFfiState
      (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10))) with
  | some (.error _ _ _ _, _) => true
  | _ => false)

def isErrorStepped {α σ : Type} : Option (PanValueFfiSteppedResult α σ) → Bool
  | some (.error _ _ _ _, _) => true
  | _ => false

def statefulNormalCallRejected : Bool :=
  isErrorStepped
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("skip", [], .skip)] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "skip" [])

#guard statefulNormalCallRejected

def statefulBreakCallRejected : Bool :=
  isErrorStepped
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("break", [], .break)] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "break" [])

def statefulContinueCallRejected : Bool :=
  isErrorStepped
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("continue", [], .continue)] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "continue" [])

#guard statefulBreakCallRejected
#guard statefulContinueCallRejected

def statefulMissingCallRejected : Bool :=
  isErrorStepped
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "missing" [])

#guard statefulMissingCallRejected

def errorPreservesCalleeLocal (expected : Word 64) :
    Option (PanValueFfiSteppedResult (Word 64) Unit) → Bool
  | some (.error locals _ _ _, _) => isWordLocal expected (locals "p")
  | _ => false

def errorEmptiesLocals :
    Option (PanValueFfiSteppedResult (Word 64) Unit) → Bool
  | some (.error locals _ _ _, _) => isWordLocal 9 (locals "p") == false
  | _ => false

def statefulBreakParamPreservesLocal : Bool :=
  errorPreservesCalleeLocal 9
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("breakp", ["p"], .break)] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "breakp" [.const (BitVec.ofNat 64 9)])

def statefulContinueParamPreservesLocal : Bool :=
  errorPreservesCalleeLocal 9
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("contp", ["p"], .continue)] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "contp" [.const (BitVec.ofNat 64 9)])

def statefulFallThroughParamPreservesLocal : Bool :=
  errorPreservesCalleeLocal 9
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("skipp", ["p"], .skip)] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "skipp" [.const (BitVec.ofNat 64 9)])

def statefulCalleeErrorEmptiesLocals : Bool :=
  errorEmptiesLocals
    (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("errp", ["p"], .assign .local "q" (.const (BitVec.ofNat 64 7)))]
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "errp" [.const (BitVec.ofNat 64 9)])

#guard statefulBreakParamPreservesLocal
#guard statefulContinueParamPreservesLocal
#guard statefulFallThroughParamPreservesLocal
#guard statefulCalleeErrorEmptiesLocals

def statefulExtCallProgram : Option (Word 64 × Nat × Nat) :=
  (evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 30 (fun _ => none) (fun _ => none) statefulTestMemory
      statefulTestFfiState
      (.seq (.extCall "echo" (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 1)))
        (.return (.loadByte (.const (BitVec.ofNat 64 8)))))
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).map
    fun result => match result.1 with
      | .returned _ _ _ ffi [.word value] => (value, result.2, ffi.ioEvents.length)
      | _ => (BitVec.ofNat 64 0, 0, 0)

#guard statefulExtCallProgram = some (BitVec.ofNat 64 0x42, 9, 1)

def statefulExactPublicProgramState : PanValueFfiExactProgramState (Word 64) Unit :=
  { legacy := statefulPublicProgramState
    memoryAccess := panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel }

#guard
  isErrorControl (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
    statefulTestPrimitive statefulTestHandler 30
    [.function
       { name := "oversized", inline := false, exported := true, params := [],
         body := .return statefulOversizedValues,
         returnShape := statefulOversizedShape }]
    "oversized" [])

#guard
  isErrorControl (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
    statefulTestPrimitive statefulTestHandler 30
    [.exnDecl "Oversized" statefulOversizedShape,
     .function
       { name := "raisesOversized", inline := false, exported := true, params := [],
         body := .raise "Oversized" statefulOversizedValues,
         returnShape := .one }]
    "raisesOversized" [])

def statefulPublicProgram : Option (Word 64 × Nat) :=
  (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq (.extCall "echo" (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)))
            (.return (.loadByte (.const (BitVec.ofNat 64 8)))),
          returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).bind
    fun result => match result with
      | .returned _ _ _ ffi [.word value] => some (value, ffi.ioEvents.length)
      | _ => none

#guard statefulPublicProgram = some (BitVec.ofNat 64 0x42, 1)

def statefulExactPublicProgram : Option (Word 64 × Nat) :=
  (evalPanValueFfiExactProgram statefulTestContext statefulExactPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq (.extCall "echo" (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)))
            (.return (.loadByte (.const (BitVec.ofNat 64 8)))),
          returnShape := .one }]
      "main" []).bind
    fun result => match result with
      | .returned _ _ _ ffi [.word value] => some (value, ffi.ioEvents.length)
      | _ => none

#guard statefulExactPublicProgram = some (BitVec.ofNat 64 0x42, 1)

/- Cake's panSem store32/storeByte paths use the supplied fixed-width memory
   operations, rather than the compatibility whole-cell update.  Keep both
   byte-order and alignment visible at the exact program boundary. -/
def statefulExactStore32Program : Option (Word 64 × Nat) :=
  (evalPanValueFfiExactProgram statefulTestContext statefulExactPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq (.store32 (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 0x11223344)))
            (.return (.load32 (.const (BitVec.ofNat 64 8)))),
          returnShape := .one }]
      "main" []).bind
    fun result => match result with
      | .returned _ _ _ _ [.word value] => some (value, 1)
      | _ => none

def statefulExactStoreByteProgram : Option (Word 64 × Nat) :=
  (evalPanValueFfiExactProgram statefulTestContext statefulExactPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq (.storeByte (.const (BitVec.ofNat 64 9))
              (.const (BitVec.ofNat 64 0xab)))
            (.return (.loadByte (.const (BitVec.ofNat 64 9)))),
          returnShape := .one }]
      "main" []).bind
    fun result => match result with
      | .returned _ _ _ _ [.word value] => some (value, 1)
      | _ => none

#guard statefulExactStore32Program = some (BitVec.ofNat 64 0x11223344, 1)
#guard statefulExactStoreByteProgram = some (BitVec.ofNat 64 0xab, 1)

#guard
  match evalPanValueFfiExactProgramStepped statefulTestContext
      statefulExactPublicProgramState statefulTestPrimitive statefulTestHandler 30
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq (.extCall "echo" (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)))
            (.return (.loadByte (.const (BitVec.ofNat 64 8)))),
          returnShape := .one }]
      "main" [] with
  | some (.returned _ _ _ ffi [.word value], _steps) =>
      value == BitVec.ofNat 64 0x42 && ffi.ioEvents.length == 1
  | _ => false

example :
    (evalPanValueFfiProgramStepped statefulTestContext
      statefulPublicProgramState statefulTestPrimitive statefulTestHandler
      30 [] "missing" []).map Prod.fst =
      evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
        statefulTestPrimitive statefulTestHandler 30 [] "missing" [] := by
  apply evalPanValueFfiProgramStepped_fst

#guard
    match evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.function
         { name := "badReturn", inline := false, exported := false, params := [],
           body := .return (.rStruct [.const (BitVec.ofNat 64 1),
             .const (BitVec.ofNat 64 2)]), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq (.call none "badReturn" []) (.return (.const 0)),
           returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel)) with
    | some (.error _ _ _ _) => true
    | _ => false

#guard
    isErrorControl
      (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.exnDecl "E" (.comb [.one, .one]),
       .function
         { name := "badRaise", inline := false, exported := false, params := [],
           body := .raise "E" (.const (BitVec.ofNat 64 1)), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq (.call none "badRaise" []) (.return (.const 0)),
           returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel)))

#guard
    (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 40
      [.exnDecl "E" .one,
       .function
         { name := "raiseGood", inline := false, exported := false, params := [],
           body := .raise "E" (.const (BitVec.ofNat 64 1)), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq
             (.dec "caught" .one (.const 0)
               (.call (some (none, some ("E", "missing", .skip)))
                 "raiseGood" []))
             (.return (.const 0)), returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).isNone =
      true

end Flapjack
