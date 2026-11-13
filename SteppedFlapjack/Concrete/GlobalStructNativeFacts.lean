import SteppedFlapjack.Concrete.GlobalStructActualWord
import SteppedFlapjack.PanToCrepSteps.RowColoring
import SteppedFlapjack.Concrete.NestedMachine
open Flapjack Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def literal : List (Nat × List Nat × HolLoopProg 64) :=
[(64,
  [],
  Flapjack.HolLoopProg.mark
    (Flapjack.HolLoopProg.seq
      (Flapjack.HolLoopProg.mark
        (Flapjack.HolLoopProg.seq
          (Flapjack.HolLoopProg.mark
            (Flapjack.HolLoopProg.seq
              (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
              (Flapjack.HolLoopProg.mark
                (Flapjack.HolLoopProg.seq
                  (Flapjack.HolLoopProg.mark
                    (Flapjack.HolLoopProg.assign
                      1
                      (Flapjack.HolLoopExp.op
                        (Flapjack.BinOp.sub)
                        [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 0x0000000000000010#64])))
                  (Flapjack.HolLoopProg.mark
                    (Flapjack.HolLoopProg.seq
                      (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
                      (Flapjack.HolLoopProg.mark
                        (Flapjack.HolLoopProg.seq
                          (Flapjack.HolLoopProg.mark
                            (Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0x0000000000000000#64)))
                          (Flapjack.HolLoopProg.mark
                            (Flapjack.HolLoopProg.seq
                              (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
                              (Flapjack.HolLoopProg.mark
                                (Flapjack.HolLoopProg.seq
                                  (Flapjack.HolLoopProg.mark
                                    (Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0x0000000000000000#64)))
                                  (Flapjack.HolLoopProg.mark
                                    (Flapjack.HolLoopProg.seq
                                      (Flapjack.HolLoopProg.mark
                                        (Flapjack.HolLoopProg.seq
                                          (Flapjack.HolLoopProg.mark
                                            (Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)))
                                          (Flapjack.HolLoopProg.mark
                                            (Flapjack.HolLoopProg.seq
                                              (Flapjack.HolLoopProg.mark
                                                (Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 4))
                                              (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))
                                      (Flapjack.HolLoopProg.mark
                                        (Flapjack.HolLoopProg.seq
                                          (Flapjack.HolLoopProg.mark
                                            (Flapjack.HolLoopProg.seq
                                              (Flapjack.HolLoopProg.mark
                                                (Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)))
                                              (Flapjack.HolLoopProg.mark
                                                (Flapjack.HolLoopProg.seq
                                                  (Flapjack.HolLoopProg.mark
                                                    (Flapjack.HolLoopProg.store
                                                      (Flapjack.HolLoopExp.op
                                                        (Flapjack.BinOp.add)
                                                        [Flapjack.HolLoopExp.var 1,
                                                         Flapjack.HolLoopExp.const 0x0000000000000008#64])
                                                      4))
                                                  (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))
                                          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))))))))))))))
          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))
      (Flapjack.HolLoopProg.mark
        (Flapjack.HolLoopProg.seq
          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.call none (some 65) [] none))
          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip)))))),
 (65,
  [],
  Flapjack.HolLoopProg.mark
    (Flapjack.HolLoopProg.seq
      (Flapjack.HolLoopProg.mark
        (Flapjack.HolLoopProg.seq
          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
          (Flapjack.HolLoopProg.mark
            (Flapjack.HolLoopProg.seq
              (Flapjack.HolLoopProg.mark
                (Flapjack.HolLoopProg.assign
                  1
                  (Flapjack.HolLoopExp.op
                    (Flapjack.BinOp.sub)
                    [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 0x0000000000000010#64])))
              (Flapjack.HolLoopProg.mark
                (Flapjack.HolLoopProg.seq
                  (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
                  (Flapjack.HolLoopProg.mark
                    (Flapjack.HolLoopProg.seq
                      (Flapjack.HolLoopProg.mark
                        (Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0x0000000000000007#64)))
                      (Flapjack.HolLoopProg.mark
                        (Flapjack.HolLoopProg.seq
                          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
                          (Flapjack.HolLoopProg.mark
                            (Flapjack.HolLoopProg.seq
                              (Flapjack.HolLoopProg.mark
                                (Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0x0000000000000008#64)))
                              (Flapjack.HolLoopProg.mark
                                (Flapjack.HolLoopProg.seq
                                  (Flapjack.HolLoopProg.mark
                                    (Flapjack.HolLoopProg.seq
                                      (Flapjack.HolLoopProg.mark
                                        (Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)))
                                      (Flapjack.HolLoopProg.mark
                                        (Flapjack.HolLoopProg.seq
                                          (Flapjack.HolLoopProg.mark
                                            (Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 4))
                                          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))
                                  (Flapjack.HolLoopProg.mark
                                    (Flapjack.HolLoopProg.seq
                                      (Flapjack.HolLoopProg.mark
                                        (Flapjack.HolLoopProg.seq
                                          (Flapjack.HolLoopProg.mark
                                            (Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)))
                                          (Flapjack.HolLoopProg.mark
                                            (Flapjack.HolLoopProg.seq
                                              (Flapjack.HolLoopProg.mark
                                                (Flapjack.HolLoopProg.store
                                                  (Flapjack.HolLoopExp.op
                                                    (Flapjack.BinOp.add)
                                                    [Flapjack.HolLoopExp.var 1,
                                                     Flapjack.HolLoopExp.const 0x0000000000000008#64])
                                                  4))
                                              (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))
                                      (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))))))))))))))
      (Flapjack.HolLoopProg.mark
        (Flapjack.HolLoopProg.seq
          (Flapjack.HolLoopProg.mark
            (Flapjack.HolLoopProg.assign
              1
              (Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op
                  (Flapjack.BinOp.add)
                  [Flapjack.HolLoopExp.op
                     (Flapjack.BinOp.sub)
                     [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 0x0000000000000010#64],
                   Flapjack.HolLoopExp.const 0x0000000000000008#64]))))
          (Flapjack.HolLoopProg.mark
            (Flapjack.HolLoopProg.seq
              (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.return [1]))
              (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))))]

private theorem literal_correct : compileProgHOLExact riscvConfig.isa globalStructCallPrograms = literal := by
  rw [← SteppedFlapjack.CrepToLoopSteps.callFrontend_compileProgWithStructuralLive_eq riscvConfig.isa globalStructCallPrograms globalStruct_actualCode_sources]
  rw [globalStruct_actualPrograms_eq]
  have fresh : newMainNameHOL globalStructProgram = ofString "main'" := by
    simp [newMainNameHOL,globalStructProgram,globalStructDecl,functionsHOL,freshNameMlS,mlstrAppend,
      ofString,MlString.explode_implode]
  rw [fresh]
  unfold globalStructActualInit globalStructActualBody
  rw [globalStruct_actual_initializer_eq,globalStructWitness_lowering]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW,nestedDecsHOL,
    cexpHeads]
  simp [List.range_succ,List.range_zero,Function.comp_def,nestedDecsHOL,storesHOL,crepNestedSeqHOL,
    globalStructCrepContext,mkCtxtExactHOL,compFieldHOL,sizeOfShapeHOL]
  with_unfolding_all rfl
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.CrepToLoopSteps
/-- The concrete optimized Loop table has a computable structural weight. -/
theorem globalStruct_loopCodeWeight :
    loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa globalStructCallPrograms)) = 62 := by
  rw [literal_correct]
  decide +kernel

/-- The concrete optimized Loop entry has a computable visit weight. -/
theorem globalStruct_loopEntryWeight : loopVisitWeight (optimiseHOL globalStructActualEntryLoop) = 62 := by
  obtain ⟨tail, table⟩ := globalStruct_actualLoop_first
  rw [literal_correct] at table
  have first := congrArg (fun (rows : List (Nat × List Nat × HolLoopProg 64)) => rows[0]?) table
  simp only [literal,List.getElem?_cons,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at first
  rw [← first.2.2]
  decide +kernel

open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps

private def row0 := (64,1,loopToWordCompFuncHOL 64 [] (literal[0]'(by decide)).2.2)
private def row1 := (65,1,loopToWordCompFuncHOL 65 [] (literal[1]'(by decide)).2.2)
private def cols0 := [(0,0),(13,0),(17,1),(21,1),(25,1),(29,1),(41,2),(45,1),(49,2),(53,1)]
private def cols1 := [(0,0),(2,1),(13,0),(17,1),(21,1),(25,1),(29,2),(41,3),(45,2),(49,3),(53,2),(65,1),(69,1)]
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem guard0 : countdownAllocatorGuard row0 = true := by with_unfolding_all rfl
private theorem failure0 : (RowColoring.colored row0).failure = none := by with_unfolding_all rfl
private theorem extract0 : cakeExtractColor (RowColoring.colored row0) (RowColoring.bij row0).toAllocator = cols0 := by
  have slots : (RowColoring.colored row0).nodeTag.slots = #[some (.fixed 0),some (.fixed 0),some (.fixed 2),some (.fixed 1),some (.fixed 1),some (.fixed 2),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row0).toAllocator = [(17,9),(21,8),(25,7),(29,6),(41,5),(45,4),(53,3),(49,2),(13,1),(0,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,cols0]
private theorem guard1 : countdownAllocatorGuard row1 = true := by with_unfolding_all rfl
private theorem failure1 : (RowColoring.colored row1).failure = none := by with_unfolding_all rfl
private theorem extract1 : cakeExtractColor (RowColoring.colored row1) (RowColoring.bij row1).toAllocator = cols1 := by
  have slots : (RowColoring.colored row1).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 3),some (.fixed 2),some (.fixed 2),some (.fixed 3),some (.fixed 2),some (.fixed 1),some (.fixed 1),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row1).toAllocator = [(0,12),(17,11),(21,10),(29,9),(41,8),(45,7),(53,6),(49,5),(25,4),(65,3),(69,2),(2,1),(13,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,cols1]
open Flapjack.Compiler.Backend.WordToStack.Native
def globalStructOptimizedWords := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig globalStructActualWordPrograms).2
private def coloredRow (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (colors : List (Nat × Nat)) :=
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (sptFromAList colors)) (RowColoring.input row))
theorem globalStruct_optimizedTable : globalStructOptimizedWords = [(64,1,coloredRow row0 cols0),(65,1,coloredRow row1 cols1)] := by
  unfold globalStructOptimizedWords globalStructActualWordPrograms
  rw [literal_correct]
  change [fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row0,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row1,none)] = _
  rw [RowColoring.compiled_exact row0 cols0 guard0 failure0 extract0,
    RowColoring.compiled_exact row1 cols1 guard1 failure1 extract1]
  rfl
theorem globalStruct_nativeBitmap : (compileNative riscvConfig false globalStructOptimizedWords).1 = [4] := by
  rw [globalStruct_optimizedTable]
  with_unfolding_all rfl

open Flapjack.Compiler.Backend.BackendProps
def globalStructNativeCode := (compileNative riscvConfig false globalStructOptimizedWords).2.2.2
def globalStructNativeEntry := ((sptLookup 64 (sptFromAList globalStructOptimizedWords)).getD (1,.skip)).2
def globalStructNativeEntryFrame := (compileProgNative riscvConfig false globalStructNativeEntry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
def globalStructNativeFrameSizes := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList globalStructOptimizedWords)
theorem globalStruct_nativeSafe : fixtureStackSafe globalStructNativeCode = true := by
  unfold globalStructNativeCode
  rw [globalStruct_optimizedTable]
  with_unfolding_all rfl
theorem globalStruct_nativeEntryFrame : globalStructNativeEntryFrame = 0 := by
  unfold globalStructNativeEntryFrame globalStructNativeEntry
  rw [globalStruct_optimizedTable]
  with_unfolding_all rfl
theorem globalStruct_nativeFrames : globalStructNativeFrameSizes = sptFromAList [(64,0),(65,0)] := by
  unfold globalStructNativeFrameSizes
  rw [globalStruct_optimizedTable]
  with_unfolding_all rfl

private theorem row0_exact : coloredRow row0 cols0 =
  Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.get 2 (Flapjack.WordStore.heapLength))
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.inst
        (Flapjack.WordLangInst.arith
          (Flapjack.WordLangArith.shift (Flapjack.Shift.lsl) 2 2 (Flapjack.WordRegImm.imm 0x0000000000000001#64))))
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.opCurrHeap (Flapjack.BinOp.add) 2 2)
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.inst
            (Flapjack.WordLangInst.arith
              (Flapjack.WordLangArith.binop (Flapjack.BinOp.add) 2 2 (Flapjack.WordRegImm.imm 0xfffffffffffffff0#64))))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4 0x0000000000000000#64))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.inst
                  (Flapjack.WordLangInst.mem
                    (Flapjack.WordMemOp.store)
                    4
                    (Flapjack.WordLangAddr.addr 2 0x0000000000000000#64)))
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4 0x0000000000000000#64))
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
                    (Flapjack.WordLangProgHOL.seq
                      (Flapjack.WordLangProgHOL.inst
                        (Flapjack.WordLangInst.mem
                          (Flapjack.WordMemOp.store)
                          4
                          (Flapjack.WordLangAddr.addr 2 0x0000000000000008#64)))
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
                        (Flapjack.WordLangProgHOL.call none (some 65) [0] none)))))))))))) := by with_unfolding_all rfl

private theorem row1_exact : coloredRow row1 cols1 =
  Flapjack.WordLangProgHOL.seq
  (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
  (Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.get 2 (Flapjack.WordStore.heapLength))
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.inst
        (Flapjack.WordLangInst.arith
          (Flapjack.WordLangArith.shift (Flapjack.Shift.lsl) 2 2 (Flapjack.WordRegImm.imm 0x0000000000000001#64))))
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.opCurrHeap (Flapjack.BinOp.add) 2 2)
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.inst
            (Flapjack.WordLangInst.arith
              (Flapjack.WordLangArith.binop (Flapjack.BinOp.add) 4 2 (Flapjack.WordRegImm.imm 0xfffffffffffffff0#64))))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6 0x0000000000000007#64))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.move 0 [(4, 4)])
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.inst
                  (Flapjack.WordLangInst.mem
                    (Flapjack.WordMemOp.store)
                    6
                    (Flapjack.WordLangAddr.addr 4 0x0000000000000000#64)))
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6 0x0000000000000008#64))
                  (Flapjack.WordLangProgHOL.seq
                    (Flapjack.WordLangProgHOL.move 0 [(4, 4)])
                    (Flapjack.WordLangProgHOL.seq
                      (Flapjack.WordLangProgHOL.inst
                        (Flapjack.WordLangInst.mem
                          (Flapjack.WordMemOp.store)
                          6
                          (Flapjack.WordLangAddr.addr 4 0x0000000000000008#64)))
                      (Flapjack.WordLangProgHOL.seq
                        (Flapjack.WordLangProgHOL.move 1 [(2, 2)])
                        (Flapjack.WordLangProgHOL.seq
                          (Flapjack.WordLangProgHOL.inst
                            (Flapjack.WordLangInst.mem
                              (Flapjack.WordMemOp.load)
                              2
                              (Flapjack.WordLangAddr.addr 2 0xfffffffffffffff8#64)))
                          (Flapjack.WordLangProgHOL.seq
                            (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
                            (Flapjack.WordLangProgHOL.return 0 [2])))))))))))))) := by with_unfolding_all rfl

open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
theorem globalStruct_nativeCallDepth : fullCallGraphDepth globalStructNativeFrameSizes 64 (sptFromAList globalStructOptimizedWords) = some 0 := by
  rw [globalStruct_nativeFrames, globalStruct_optimizedTable, row0_exact, row1_exact]
  simp [Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth,
    Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
    sptLookup_sptFromAList, sptAListLookup]
  split <;> simp_all [sptLookup_sptFromAList, sptAListLookup]
  all_goals obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›
  all_goals simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
    sptSize, sptFromAList, sptInsert]
  all_goals with_unfolding_all rfl
theorem globalStruct_nativeCapacity : optionLe
    (optionMap₂ max (some (max 1 (1+globalStructNativeEntryFrame)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth globalStructNativeFrameSizes 64 (sptFromAList globalStructOptimizedWords))))
    (some 2097172) := by
  rw [globalStruct_nativeEntryFrame,globalStruct_nativeCallDepth]
  decide
theorem globalStruct_nativeCompilerFacts : (fixtureRemoveLabels globalStructNativeCode).isSome = true ∧
    (fixtureCodeBytes globalStructNativeCode).length ≤ 0xecc ∧ (fixtureCodeBytes globalStructNativeCode).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels globalStructNativeCode
    rw [globalStruct_optimizedTable,row0_exact,row1_exact]
    with_unfolding_all decide
  · unfold fixtureCodeBytes globalStructNativeCode
    rw [globalStruct_optimizedTable,row0_exact,row1_exact]
    simp_rw [LabToTarget.progToBytesMap]
    with_unfolding_all decide

open Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps
theorem globalStruct_tickFactor (cfg : Flapjack.Compiler.Backend.LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf globalStructNativeCode)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  unfold globalStructNativeCode
  rw [globalStruct_optimizedTable,row0_exact,row1_exact]
  decide +kernel


open SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
theorem globalStruct_wordCodeWeight : wordCodeWeight (sptFromAList globalStructOptimizedWords) = 29 := by
  rw [globalStruct_optimizedTable,row0_exact,row1_exact]
  decide +kernel
theorem globalStruct_stackCodeWeight : stackCodeWeight (sptFromAList globalStructNativeCode) = 31 := by
  unfold globalStructNativeCode
  rw [globalStruct_optimizedTable,row0_exact,row1_exact]
  decide +kernel

end SteppedFlapjack.Concrete
