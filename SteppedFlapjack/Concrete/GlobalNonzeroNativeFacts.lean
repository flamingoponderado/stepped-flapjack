import SteppedFlapjack.Concrete.GlobalCountedMachine
import SteppedFlapjack.PanToCrepSteps.RowColoring
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def nonzeroScalarProgram : List (DeclHOL 64) :=
  [.decl .one (ofString "x") (.const 3),
    .function ⟨ofString "main",false,false,[],.return (.var .global (ofString "x")),.one⟩]
def nonzeroScalarCrep : List (MlS × List Nat × CrepProgHOL 64) :=
[(Flapjack.Basis.Pure.MlString.MlString.implode [0x6d#8, 0x61#8, 0x69#8, 0x6e#8],
  [],
  Flapjack.CrepProgHOL.seq
    (Flapjack.CrepProgHOL.seq
      (Flapjack.CrepProgHOL.dec
        1
        (Flapjack.CrepExpHOL.op
          (Flapjack.BinOp.sub)
          [Flapjack.CrepExpHOL.topAddr, Flapjack.CrepExpHOL.const 0x0000000000000008#64])
        (Flapjack.CrepProgHOL.dec
          2
          (Flapjack.CrepExpHOL.const 0x0000000000000003#64)
          (Flapjack.CrepProgHOL.seq
            (Flapjack.CrepProgHOL.store (Flapjack.CrepExpHOL.var 1) (Flapjack.CrepExpHOL.var 2))
            (Flapjack.CrepProgHOL.skip))))
      (Flapjack.CrepProgHOL.skip))
    (Flapjack.CrepProgHOL.call
      none
      (Flapjack.Basis.Pure.MlString.MlString.implode [0x6d#8, 0x61#8, 0x69#8, 0x6e#8, 0x27#8])
      [])),
 (Flapjack.Basis.Pure.MlString.MlString.implode [0x6d#8, 0x61#8, 0x69#8, 0x6e#8, 0x27#8],
  [],
  Flapjack.CrepProgHOL.return
    [Flapjack.CrepExpHOL.load
       (Flapjack.CrepExpHOL.op
         (Flapjack.BinOp.sub)
         [Flapjack.CrepExpHOL.topAddr, Flapjack.CrepExpHOL.const 0x0000000000000008#64])])]
theorem nonzeroScalar_crep : globalSourcePrograms nonzeroScalarProgram = nonzeroScalarCrep := by
  unfold globalSourcePrograms
  simp [nonzeroScalarProgram,panSimpDeclsHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.getNamesExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileDeclsExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileExpExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact]
  change compileProgDeclsHOLW (compileTopExactHOL nonzeroScalarProgram (ofString "main")) = nonzeroScalarCrep
  have noinline : (functionsHOL ((compileTopExactHOL nonzeroScalarProgram (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
    with_unfolding_all decide
  rw [compileProgDeclsHOLW,noinline,CrepInlineRoute.compileInlTopHOLExact_nil]
  with_unfolding_all rfl

open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
private def context : PanToCrepContextExact 64 := mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty
private def init : ProgHOL 64 := .store (.op .sub [.topAddr,.const 8]) (.const 3)
private def entryProg : ProgHOL 64 := .seq (.seq init .skip) (.call none (MlString.implode [0x6d,0x61,0x69,0x6e,0x27]) [])
private def bodyProg : ProgHOL 64 := .return (.load .one (.op .sub [.topAddr,.const 8]))
private theorem nonzeroEntryShape : CallFrontend context entryProg := by
  exact .seq (.base (.seq (.store (.op .sub .topAddr (.const 8)) (.const 3)) .skip)) (.tail (by simp))
private theorem bodyShape : CallFrontend context bodyProg := by
  exact .base (.ret (.load (.op .sub .topAddr (.const 8))))
private theorem entryCompile : compileProgExactHOLW context entryProg = (nonzeroScalarCrep[0]'(by decide)).2.2 := by
  simp [entryProg,init,nonzeroScalarCrep,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileStoreExactHOLW,
    compileExpExactHOLW,compileExpExactHOLWList,context,mkCtxtExactHOL,cexpHeads,nestedDecsHOL,crepNestedSeqHOL,storesHOL]
private theorem bodyCompile : compileProgExactHOLW context bodyProg = (nonzeroScalarCrep[1]'(by decide)).2.2 := by
  simp [bodyProg,nonzeroScalarCrep,compileProgExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    loadShapeBytesHOLW,sizeOfShapeHOL,context,mkCtxtExactHOL,cexpHeads]

theorem nonzeroScalar_sources : ∀ row ∈ globalSourcePrograms nonzeroScalarProgram,
    ∃ (ctx : PanToCrepContextExact 64) (q : ProgHOL 64), row.2.2 = compileProgExactHOLW ctx q ∧ CallFrontend ctx q := by
  rw [nonzeroScalar_crep]
  intro row member
  simp only [nonzeroScalarCrep,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact ⟨context,entryProg,entryCompile.symm,nonzeroEntryShape⟩
  · exact ⟨context,bodyProg,bodyCompile.symm,bodyShape⟩

def nonzeroScalarLoop : List (Nat × List Nat × HolLoopProg 64) :=
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
                        [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 0x0000000000000008#64])))
                  (Flapjack.HolLoopProg.mark
                    (Flapjack.HolLoopProg.seq
                      (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
                      (Flapjack.HolLoopProg.mark
                        (Flapjack.HolLoopProg.seq
                          (Flapjack.HolLoopProg.mark
                            (Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0x0000000000000003#64)))
                          (Flapjack.HolLoopProg.mark
                            (Flapjack.HolLoopProg.seq
                              (Flapjack.HolLoopProg.mark
                                (Flapjack.HolLoopProg.seq
                                  (Flapjack.HolLoopProg.mark
                                    (Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)))
                                  (Flapjack.HolLoopProg.mark
                                    (Flapjack.HolLoopProg.seq
                                      (Flapjack.HolLoopProg.mark
                                        (Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3))
                                      (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))
                              (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))))))))
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
        (Flapjack.HolLoopProg.assign
          1
          (Flapjack.HolLoopExp.load
            (Flapjack.HolLoopExp.op
              (Flapjack.BinOp.sub)
              [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 0x0000000000000008#64]))))
      (Flapjack.HolLoopProg.mark
        (Flapjack.HolLoopProg.seq
          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.return [1]))
          (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))]
theorem nonzeroScalar_loop : compileProgHOLExact riscvConfig.isa (globalSourcePrograms nonzeroScalarProgram) = nonzeroScalarLoop := by
  rw [← callFrontend_compileProgWithStructuralLive_eq riscvConfig.isa _ nonzeroScalar_sources,nonzeroScalar_crep]
  with_unfolding_all rfl

open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToStack.Native
private def row0 := (64,1,loopToWordCompFuncHOL 64 [] (nonzeroScalarLoop[0]'(by decide)).2.2)
private def row1 := (65,1,loopToWordCompFuncHOL 65 [] (nonzeroScalarLoop[1]'(by decide)).2.2)
private def cols0 := [(0, 0), (9, 0), (13, 1), (17, 1), (21, 1), (25, 1), (33, 2), (37, 1)]
private def cols1 := [(0, 0), (2, 1), (5, 0), (9, 1), (13, 1), (17, 1), (21, 1)]
private theorem guard0 : countdownAllocatorGuard row0 = true := by with_unfolding_all rfl
private theorem failure0 : (RowColoring.colored row0).failure = none := by with_unfolding_all rfl
private theorem extract0 : cakeExtractColor (RowColoring.colored row0) (RowColoring.bij row0).toAllocator = cols0 := by
  have slots : (RowColoring.colored row0).nodeTag.slots = #[some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 0), some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 0),
  some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 2), some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1),
  some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1), some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1),
  some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1), some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row0).toAllocator = [(13, 7), (17, 6), (21, 5), (25, 4), (37, 3), (33, 2), (9, 1), (0, 0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,cols0]
private theorem guard1 : countdownAllocatorGuard row1 = true := by with_unfolding_all rfl
private theorem failure1 : (RowColoring.colored row1).failure = none := by with_unfolding_all rfl
private theorem extract1 : cakeExtractColor (RowColoring.colored row1) (RowColoring.bij row1).toAllocator = cols1 := by
  have slots : (RowColoring.colored row1).nodeTag.slots = #[some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 0), some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1),
  some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1), some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1),
  some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1), some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 1),
  some (Flapjack.RiscV.CakeRegAlloc.CakeNodeTag.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row1).toAllocator = [(0, 6), (9, 5), (13, 4), (17, 3), (21, 2), (2, 1), (5, 0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,cols1]
private def coloredRow (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (colors : List (Nat × Nat)) :=
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (sptFromAList colors)) (RowColoring.input row))
private theorem optimizedTable : globalSourceWords nonzeroScalarProgram = [(64,1,coloredRow row0 cols0),(65,1,coloredRow row1 cols1)] := by
  unfold globalSourceWords globalSourceRaw
  rw [nonzeroScalar_loop]
  change [fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row0,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row1,none)] = _
  rw [RowColoring.compiled_exact row0 cols0 guard0 failure0 extract0,
    RowColoring.compiled_exact row1 cols1 guard1 failure1 extract1]
  rfl

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
              (Flapjack.WordLangArith.binop (Flapjack.BinOp.add) 2 2 (Flapjack.WordRegImm.imm 0xfffffffffffffff8#64))))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4 0x0000000000000003#64))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.inst
                  (Flapjack.WordLangInst.mem
                    (Flapjack.WordMemOp.store)
                    4
                    (Flapjack.WordLangAddr.addr 2 0x0000000000000000#64)))
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
                  (Flapjack.WordLangProgHOL.call none (some 65) [0] none))))))))) := by with_unfolding_all rfl
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
            (Flapjack.WordLangInst.mem
              (Flapjack.WordMemOp.load)
              2
              (Flapjack.WordLangAddr.addr 2 0xfffffffffffffff8#64)))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
            (Flapjack.WordLangProgHOL.return 0 [2])))))) := by with_unfolding_all rfl

theorem nonzeroScalar_bitmap : globalSourceBitmaps nonzeroScalarProgram = [4] := by
  unfold globalSourceBitmaps globalSourceNative
  rw [optimizedTable,row0_exact,row1_exact]
  with_unfolding_all rfl
theorem nonzeroScalar_safe : fixtureStackSafe (globalSourceCode nonzeroScalarProgram) = true := by
  unfold globalSourceCode globalSourceNative
  rw [optimizedTable,row0_exact,row1_exact]
  with_unfolding_all decide
theorem nonzeroScalar_facts : (fixtureRemoveLabels (globalSourceCode nonzeroScalarProgram)).isSome = true ∧
    (fixtureCodeBytes (globalSourceCode nonzeroScalarProgram)).length ≤ 0xecc ∧
    (fixtureCodeBytes (globalSourceCode nonzeroScalarProgram)).length % 4 = 0 := by
  unfold fixtureRemoveLabels fixtureCodeBytes globalSourceCode globalSourceNative
  rw [optimizedTable,row0_exact,row1_exact]
  simp_rw [LabToTarget.progToBytesMap]
  with_unfolding_all decide
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
private theorem frame : globalSourceFrame nonzeroScalarProgram = 0 := by
  unfold globalSourceFrame globalSourceEntry
  rw [optimizedTable,row0_exact,row1_exact]
  with_unfolding_all rfl
private theorem frames : globalSourceFrames nonzeroScalarProgram = sptFromAList [(64,0),(65,0)] := by
  unfold globalSourceFrames
  rw [optimizedTable,row0_exact,row1_exact]
  with_unfolding_all rfl
private theorem depth : fullCallGraphDepth (globalSourceFrames nonzeroScalarProgram) 64
    (sptFromAList (globalSourceWords nonzeroScalarProgram)) = some 0 := by
  rw [frames,optimizedTable,row0_exact,row1_exact]
  simp [fullCallGraphDepth,callGraphDepth,sptLookup_sptFromAList,sptAListLookup]
  split <;> simp_all [sptLookup_sptFromAList,sptAListLookup]
  all_goals obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›
  all_goals simp [callGraphDepth,sptSize,sptFromAList,sptInsert]
  all_goals with_unfolding_all rfl
theorem nonzeroScalar_capacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame nonzeroScalarProgram)))
    (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames nonzeroScalarProgram) 64
      (sptFromAList (globalSourceWords nonzeroScalarProgram))))) (some 2097172) := by
  rw [frame,depth]
  decide

open Flapjack.Compiler.Backend.StackLang SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
theorem nonzeroScalar_loopWeight : loopCodeWeight (sptFromAList
    (compileProgHOLExact riscvConfig.isa (globalSourcePrograms nonzeroScalarProgram))) = 42 := by
  rw [nonzeroScalar_loop]
  decide +kernel
theorem nonzeroScalar_wordWeight : wordCodeWeight (sptFromAList (globalSourceWords nonzeroScalarProgram)) = 19 := by
  rw [optimizedTable,row0_exact,row1_exact]
  decide +kernel
theorem nonzeroScalar_stackWeight : stackCodeWeight (sptFromAList (globalSourceCode nonzeroScalarProgram)) = 23 := by
  unfold globalSourceCode globalSourceNative
  rw [optimizedTable,row0_exact,row1_exact]
  decide +kernel
theorem nonzeroScalar_tickFactor (cfg : Flapjack.Compiler.Backend.LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode nonzeroScalarProgram))) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  unfold globalSourceCode globalSourceNative
  rw [optimizedTable,row0_exact,row1_exact]
  decide +kernel
end SteppedFlapjack.Concrete
