import SteppedFlapjack.Concrete.CountedApplications
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

def badShift : Prog (RiscV.Word 64) := .return (.shift .lsl (.const 1) (.const 64))
example : Supported badShift := by
  constructor
  · exact .ret (.shift .lsl (.const _) (.const _))
  · simp [badShift,ProgByteRanged,ExpByteRanged]
example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL badShift)).structs []
      (executableState (progToHOL badShift)).baseAddress (executableState (progToHOL badShift)).topAddress
      panSemBitVec64BytesInWord 1 (executableState (progToHOL badShift)).locals (executableState (progToHOL badShift)).globals
      (executableState (progToHOL badShift)).memory (executableState (progToHOL badShift)).ffi badShift
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL badShift)))) =
      some (.error (executableState (progToHOL badShift)).locals (executableState (progToHOL badShift)).globals
        (executableState (progToHOL badShift)).memory (executableState (progToHOL badShift)).ffi,0) := by
  simp [badShift,evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,evalPanValueExpCounted,
    evalPanValueExp,panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,
    panSemWordModel,RiscV.panRiscVMemoryModel,RiscV.panRiscVShift]
end SteppedFlapjack.Concrete
