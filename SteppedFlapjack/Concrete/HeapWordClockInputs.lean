import SteppedFlapjack.Concrete.HeapWordMachine

/-! Concrete component weights of the heap store/load machine clock. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem heapStackWeight : stackCodeWeight (sptFromAList (supportedNative heapWordWitness).2.2.2) = 17 := by
  rw [heapNativeLiteral_eq]
  decide +kernel
private theorem heapWordWeight : wordCodeWeight (sptFromAList (supportedAllocated heapWordWitness).2) = 15 := by
  rw [heapOptimizedLiteral_eq]
  decide +kernel



private theorem heapEntries : functionsHOL (heapHOLFunctions.map DeclHOL.function) =
    [(ofString "main",[],progToHOL heapWordWitness,ShapeHOL.one)] := by
  simp only [heapHOLFunctions,heapFunctions,List.map,funDeclToHOL,functionsHOL,shapeToHOL]
private theorem heapSimpBody : panSimpCompileHOL (progToHOL heapWordWitness) = progToHOL heapWordWitness := by
  simp only [heapWordWitness,progToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL]
private theorem heapTableWeight : SimpVisits.simpTableFactor (functionsHOL (heapHOLFunctions.map DeclHOL.function)) = 4 := by
  rw [heapEntries]
  have generic (p : ProgHOL 64) : SimpVisits.simpTableFactor [(ofString "main",[],p,ShapeHOL.one)] =
      1 + max (SimpVisits.hw (panSimpCompileHOL p)) 0 := by rfl
  have hweight : SimpVisits.hw (progToHOL heapWordWitness) = 3 := by
    simp only [heapWordWitness,progToHOL,SimpVisits.hw]
  have h := generic (progToHOL heapWordWitness)
  have w := (congrArg SimpVisits.hw heapSimpBody).trans hweight
  have rhs : 1 + max (SimpVisits.hw (panSimpCompileHOL (progToHOL heapWordWitness))) 0 = 4 := by
    rw [w]
    decide
  exact h.trans rhs

private theorem heapBodyWeight : SimpVisits.hw (progToHOL (panSimpProg heapWordWitness)) = 3 := by
  simp [heapWordWitness,panSimpProg,seqAssoc,retToTail,smartSeq,seqCallRet,progToHOL,expToHOL,SimpVisits.hw]
private theorem heapCodeWeight : CrepSteps.codeWeight (crepPrograms (progToHOL (panSimpProg heapWordWitness))) = 7 := by
  rw [heapCrepTable]
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,twoPrograms]
theorem heapClock_callFactor (ctx : CrepToLoopContextExact) (clock : Nat) :
    callClockFactor ctx ((crepPrograms (progToHOL (panSimpProg heapWordWitness))).map (fun row => (row.2.1,row.2.2))) clock
      (.seq .skip (.call none (entryName (progToHOL (panSimpProg heapWordWitness))) [])) = 174 := by
  rw [heapCrepTable]
  simp [callClockFactor,callTableCost,twoPrograms,callSyntaxCost,callExpressionCost,callArgumentsCost,
    compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]


/-- The source and generated-code weights in the concrete heap clock. -/
theorem heapClock_staticWeights :
    SimpVisits.simpTableFactor (functionsHOL (heapHOLFunctions.map DeclHOL.function)) = 4 ∧
    SimpVisits.hw (progToHOL (panSimpProg heapWordWitness)) = 3 ∧
    CrepSteps.codeWeight (crepPrograms (progToHOL (panSimpProg heapWordWitness))) = 7 ∧
    loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa (crepPrograms (progToHOL (panSimpProg heapWordWitness))))) = 42 ∧
    wordCodeWeight (sptFromAList (supportedAllocated heapWordWitness).2) = 15 ∧
    stackCodeWeight (sptFromAList (supportedNative heapWordWitness).2.2.2) = 17 :=
  ⟨heapTableWeight,heapBodyWeight,heapCodeWeight,heapLoopWeight,heapWordWeight,heapStackWeight⟩

/-- The concrete heap code gives the machine backend its fixed clock factor. -/
theorem heapClock_targetFactor (cfg : Flapjack.Compiler.Backend.LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (supportedNative heapWordWitness).2.2.2)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  rw [heapNativeLiteral_eq]
  unfold heapNativeLiteral
  decide +kernel
end SteppedFlapjack.Concrete
