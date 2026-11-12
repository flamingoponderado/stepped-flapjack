import SteppedFlapjack.Concrete.Phase7Machine
import SteppedFlapjack.Concrete.HeapWordWitness
import SteppedFlapjack.Concrete.Phase7NativeFacts
import SteppedFlapjack.PanToCrepSteps.RowColoring
import SteppedFlapjack.Concrete.FixtureCompilerFacts
/-! Kernel-checked compiler and machine guards for the heap store/load witness. -/
namespace SteppedFlapjack.Concrete
open SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def heapCallee : CrepProgHOL 64 :=
 .seq (.dec 1 (.const 0xa1000100) (.dec 2 (.const 7) (.seq (.store (.var 1) (.var 2)) .skip)))
      (.return [.load (.const 0xa1000100)])

private theorem heapCallee_eq : supportedCallee (progToHOL (panSimpProg heapWordWitness)) = heapCallee := by
  simp only [supportedCallee, frontendContext, heapWordWitness, panSimpProg, retToTail, seqAssoc, smartSeq, seqCallRet, progToHOL, declarations, singleEntry_compileTop]
  simp only [ctxtFcExactHOL, mkCtxtExactHOL, compileProgExactHOLW, compileExpExactHOLW, compileStoreExactHOLW, compileReturnExactHOLW, expToHOL, shapeToHOL]
  with_unfolding_all rfl


private def heapLoop : HolLoopProg 64 :=
Flapjack.HolLoopProg.mark
  (Flapjack.HolLoopProg.seq
    (Flapjack.HolLoopProg.mark
      (Flapjack.HolLoopProg.seq
        (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
        (Flapjack.HolLoopProg.mark
          (Flapjack.HolLoopProg.seq
            (Flapjack.HolLoopProg.mark
              (Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0x00000000a1000100#64)))
            (Flapjack.HolLoopProg.mark
              (Flapjack.HolLoopProg.seq
                (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))
                (Flapjack.HolLoopProg.mark
                  (Flapjack.HolLoopProg.seq
                    (Flapjack.HolLoopProg.mark
                      (Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0x0000000000000007#64)))
                    (Flapjack.HolLoopProg.mark
                      (Flapjack.HolLoopProg.seq
                        (Flapjack.HolLoopProg.mark
                          (Flapjack.HolLoopProg.seq
                            (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)))
                            (Flapjack.HolLoopProg.mark
                              (Flapjack.HolLoopProg.seq
                                (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3))
                                (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))
                        (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip))))))))))))
    (Flapjack.HolLoopProg.mark
      (Flapjack.HolLoopProg.seq
        (Flapjack.HolLoopProg.mark
          (Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.const 0x00000000a1000100#64))))
        (Flapjack.HolLoopProg.mark
          (Flapjack.HolLoopProg.seq
            (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.return [1]))
            (Flapjack.HolLoopProg.mark (Flapjack.HolLoopProg.skip)))))))

private theorem heapLoop_eq : twoCallee riscvConfig.isa (ofString "main") (entryName (progToHOL (panSimpProg heapWordWitness))) (supportedCallee (progToHOL (panSimpProg heapWordWitness))) = heapLoop := by
  rw [heapCallee_eq]
  unfold twoCallee heapCallee
  with_unfolding_all rfl


/-- The generated Crep table has the fixed tail entry and the heap body. -/
theorem heapCrepTable : crepPrograms (progToHOL (panSimpProg heapWordWitness)) =
    twoPrograms (ofString "main") (entryName (progToHOL (panSimpProg heapWordWitness)))
      (.seq (.dec 1 (.const 0xa1000100) (.dec 2 (.const 7) (.seq (.store (.var 1) (.var 2)) .skip)))
        (.return [.load (.const 0xa1000100)])) := by
  have hs : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))), heapWordWitness_ranged⟩
  rw [supported_crepPrograms _ (supported_panSimp _ hs).1, heapCallee_eq]
  rfl

/-- The optimized Loop table has a concrete structural weight. -/
theorem heapLoopWeight :
    loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
      (crepPrograms (progToHOL (panSimpProg heapWordWitness))))) = 42 := by
  have hs : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))), heapWordWitness_ranged⟩
  have hc := supported_crepPrograms (panSimpProg heapWordWitness) (supported_panSimp _ hs).1
  have shape := supportedCallee_scalar (panSimpProg heapWordWitness) (supported_panSimp _ hs).1
  have fresh : ofString "main" ≠ entryName (progToHOL (panSimpProg heapWordWitness)) := Ne.symm (entryName_fresh _)
  rw [hc, ← twoLoopPrograms_eq riscvConfig.isa _ _ _ shape, twoLoops_exact _ _ _ _ fresh, heapLoop_eq]
  with_unfolding_all decide


private def heapRaw : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
[(64,
  1,
  Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.skip)
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.call none (some 65) [0] none)
      (Flapjack.WordLangProgHOL.skip))),
 (65,
  1,
  Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.skip)
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0x00000000a1000100#64))
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.skip)
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0x0000000000000007#64))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 6))
                (Flapjack.WordLangProgHOL.seq
                  (Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 2)
                  (Flapjack.WordLangProgHOL.skip)))
              (Flapjack.WordLangProgHOL.skip))))))
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.assign
        4
        (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.const 0x00000000a1000100#64)))
      (Flapjack.WordLangProgHOL.seq (Flapjack.WordLangProgHOL.return 0 [4]) (Flapjack.WordLangProgHOL.skip))))]

private theorem heapRaw_eq : supportedWordPrograms heapWordWitness = heapRaw := by
  have hs : CallFreeSupported heapWordWitness := by
    refine ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))), heapWordWitness_ranged⟩
  have hc := supported_crepPrograms (panSimpProg heapWordWitness) (supported_panSimp _ hs).1
  have shape := supportedCallee_scalar (panSimpProg heapWordWitness) (supported_panSimp _ hs).1
  unfold supportedWordPrograms
  rw [hc, ← twoLoopPrograms_eq riscvConfig.isa _ _ _ shape]
  have fresh : ofString "main" ≠ entryName (progToHOL (panSimpProg heapWordWitness)) := Ne.symm (entryName_fresh _)
  rw [twoLoops_exact _ _ _ _ fresh, heapLoop_eq]
  with_unfolding_all rfl


open Flapjack.Compiler.Backend Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
private def row0 := heapRaw[0]'(by decide)
private def row1 := heapRaw[1]'(by decide)
private def cols0 := [(0,0)]
private def cols1 := [(0,0),(2,1),(9,0),(21,1),(25,2),(29,1),(33,1)]
private theorem guard0 : countdownAllocatorGuard row0 = true := by with_unfolding_all rfl
private theorem failure0 : (RowColoring.colored row0).failure = none := by with_unfolding_all rfl
private theorem extract0 : cakeExtractColor (RowColoring.colored row0) (RowColoring.bij row0).toAllocator = cols0 := by with_unfolding_all rfl
private theorem guard1 : countdownAllocatorGuard row1 = true := by with_unfolding_all rfl
private theorem failure1 : (RowColoring.colored row1).failure = none := by with_unfolding_all rfl
private theorem extract1 : cakeExtractColor (RowColoring.colored row1) (RowColoring.bij row1).toAllocator = cols1 := by
  have slots : (RowColoring.colored row1).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 2),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row1).toAllocator = [(0,6),(25,5),(21,4),(29,3),(33,2),(2,1),(9,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,cols1]
private def coloredRow (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (colors : List (Nat × Nat)) :=
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (sptFromAList colors)) (RowColoring.input row))
private theorem heapOptimized_eq : (supportedAllocated heapWordWitness).2 = [(64,1,coloredRow row0 cols0),(65,1,coloredRow row1 cols1)] := by
  unfold supportedAllocated
  rw [heapRaw_eq]
  change [fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row0,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row1,none)] = _
  rw [RowColoring.compiled_exact row0 cols0 guard0 failure0 extract0,
    RowColoring.compiled_exact row1 cols1 guard1 failure1 extract1]
  rfl


def heapOptimizedLiteral : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
[(64,
  1,
  Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
    (Flapjack.WordLangProgHOL.call none (some 65) [0] none)),
 (65,
  1,
  Flapjack.WordLangProgHOL.seq
    (Flapjack.WordLangProgHOL.move 1 [(0, 0)])
    (Flapjack.WordLangProgHOL.seq
      (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 0x0000000000000007#64))
      (Flapjack.WordLangProgHOL.seq
        (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4 0x00000000a1000100#64))
        (Flapjack.WordLangProgHOL.seq
          (Flapjack.WordLangProgHOL.inst
            (Flapjack.WordLangInst.mem
              (Flapjack.WordMemOp.store)
              2
              (Flapjack.WordLangAddr.addr 4 0x0000000000000000#64)))
          (Flapjack.WordLangProgHOL.seq
            (Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 0x00000000a1000100#64))
            (Flapjack.WordLangProgHOL.seq
              (Flapjack.WordLangProgHOL.inst
                (Flapjack.WordLangInst.mem
                  (Flapjack.WordMemOp.load)
                  2
                  (Flapjack.WordLangAddr.addr 2 0x0000000000000000#64)))
              (Flapjack.WordLangProgHOL.seq
                (Flapjack.WordLangProgHOL.move 0 [(2, 2)])
                (Flapjack.WordLangProgHOL.return 0 [2]))))))))]
theorem heapOptimizedLiteral_eq : (supportedAllocated heapWordWitness).2 = heapOptimizedLiteral := by
  rw [heapOptimized_eq]
  unfold heapOptimizedLiteral
  congr 2
  all_goals with_unfolding_all rfl


def heapNativeLiteral : List (Nat × Flapjack.Compiler.Backend.StackLang.HolProg 64) :=
[(5,
  Flapjack.Compiler.Backend.StackLang.Prog.seq
    (Flapjack.Compiler.Backend.StackLang.Prog.get 22 (Flapjack.Compiler.Backend.StackLang.StoreName.handler))
    (Flapjack.Compiler.Backend.StackLang.Prog.seq
      (Flapjack.Compiler.Backend.StackLang.Prog.stackSetSize 22)
      (Flapjack.Compiler.Backend.StackLang.Prog.seq
        (Flapjack.Compiler.Backend.StackLang.Prog.skip)
        (Flapjack.Compiler.Backend.StackLang.Prog.seq
          (Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2)
          (Flapjack.Compiler.Backend.StackLang.Prog.seq
            (Flapjack.Compiler.Backend.StackLang.Prog.set (Flapjack.Compiler.Backend.StackLang.StoreName.handler) 22)
            (Flapjack.Compiler.Backend.StackLang.Prog.seq
              (Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 1)
              (Flapjack.Compiler.Backend.StackLang.Prog.seq
                (Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3)
                (Flapjack.Compiler.Backend.StackLang.Prog.raise 22)))))))),
 (6,
  Flapjack.Compiler.Backend.StackLang.Prog.seq
    (Flapjack.Compiler.Backend.StackLang.Prog.storeConsts 22 23 none)
    (Flapjack.Compiler.Backend.StackLang.Prog.ret 0)),
 (64,
  Flapjack.Compiler.Backend.StackLang.Prog.seq
    (Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0)
    (Flapjack.Compiler.Backend.StackLang.Prog.seq
      (Flapjack.Compiler.Backend.StackLang.Prog.skip)
      (Flapjack.Compiler.Backend.StackLang.Prog.seq
        (Flapjack.Compiler.Backend.StackLang.Prog.skip)
        (Flapjack.Compiler.Backend.StackLang.Prog.call none (Sum.inl 65) none)))),
 (65,
  Flapjack.Compiler.Backend.StackLang.Prog.seq
    (Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0)
    (Flapjack.Compiler.Backend.StackLang.Prog.seq
      (Flapjack.Compiler.Backend.StackLang.Prog.skip)
      (Flapjack.Compiler.Backend.StackLang.Prog.seq
        (Flapjack.Compiler.Backend.StackLang.Prog.inst
          (Flapjack.Compiler.Encoders.Asm.HolInst.const 1 0x0000000000000007#64))
        (Flapjack.Compiler.Backend.StackLang.Prog.seq
          (Flapjack.Compiler.Backend.StackLang.Prog.inst
            (Flapjack.Compiler.Encoders.Asm.HolInst.const 2 0x00000000a1000100#64))
          (Flapjack.Compiler.Backend.StackLang.Prog.seq
            (Flapjack.Compiler.Backend.StackLang.Prog.inst
              (Flapjack.Compiler.Encoders.Asm.HolInst.mem
                (Flapjack.WordMemOp.store)
                1
                (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 2 0x0000000000000000#64)))
            (Flapjack.Compiler.Backend.StackLang.Prog.seq
              (Flapjack.Compiler.Backend.StackLang.Prog.inst
                (Flapjack.Compiler.Encoders.Asm.HolInst.const 1 0x00000000a1000100#64))
              (Flapjack.Compiler.Backend.StackLang.Prog.seq
                (Flapjack.Compiler.Backend.StackLang.Prog.inst
                  (Flapjack.Compiler.Encoders.Asm.HolInst.mem
                    (Flapjack.WordMemOp.load)
                    1
                    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 1 0x0000000000000000#64)))
                (Flapjack.Compiler.Backend.StackLang.Prog.seq
                  (Flapjack.Compiler.Backend.StackLang.Prog.skip)
                  (Flapjack.Compiler.Backend.StackLang.Prog.ret 0)))))))))]

theorem heapNativeLiteral_eq : (supportedNative heapWordWitness).2.2.2 = heapNativeLiteral := by
  unfold supportedNative
  rw [heapOptimizedLiteral_eq]
  with_unfolding_all rfl

theorem heapNative_safe : fixtureStackSafe (supportedNative heapWordWitness).2.2.2 = true := by
  rw [heapNativeLiteral_eq]
  with_unfolding_all rfl

theorem heapNative_compilerFacts : (fixtureRemoveLabels (supportedNative heapWordWitness).2.2.2).isSome = true ∧
    (fixtureCodeBytes (supportedNative heapWordWitness).2.2.2).length ≤ 0xecc ∧
    (fixtureCodeBytes (supportedNative heapWordWitness).2.2.2).length % 4 = 0 := by
  rw [heapNativeLiteral_eq]
  constructor
  · unfold fixtureRemoveLabels
    with_unfolding_all decide
  · unfold fixtureCodeBytes
    simp_rw [Flapjack.Compiler.Backend.LabToTarget.progToBytesMap]
    with_unfolding_all decide


open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordDepth
open Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
private def heapEntry := ((sptLookup 64 (sptFromAList heapOptimizedLiteral)).getD (1,.skip)).2
private def heapEntryFrame := (compileProgNative riscvConfig false heapEntry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
private def heapFrames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList heapOptimizedLiteral)
private theorem heapEntryFrame_eq : heapEntryFrame = 0 := by with_unfolding_all rfl
private theorem heapFrames_eq : heapFrames = sptFromAList [(64,0),(65,0)] := by with_unfolding_all rfl
private theorem heapDepth_eq : fullCallGraphDepth heapFrames 64 (sptFromAList heapOptimizedLiteral) = some 0 := by
  rw [heapFrames_eq]
  simp [fullCallGraphDepth,callGraphDepth, sptLookup_sptFromAList, sptAListLookup, heapOptimizedLiteral]
  split <;> simp_all [sptLookup_sptFromAList,sptAListLookup]
  all_goals obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›
  all_goals simp [callGraphDepth,sptSize,sptFromAList,sptInsert]
  all_goals with_unfolding_all rfl

theorem heapNative_capacity : optionLe
    (optionMap₂ max (some (max 1 (1+heapEntryFrame)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth heapFrames 64 (sptFromAList heapOptimizedLiteral))))
    (some 2097172) := by
  rw [heapEntryFrame_eq,heapDepth_eq]
  decide


end SteppedFlapjack.Concrete
