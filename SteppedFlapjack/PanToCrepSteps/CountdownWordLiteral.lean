import SteppedFlapjack.PanToCrepSteps.CountdownStructuralLab

/-! A kernel-checked concrete Word frontend for the countdown example. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps

/-- Word program generated for the countdown variable `x`. -/
def countdownWordLiteral (initial returned : BitVec 64) :
    List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  [(64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),
   (65,1,.seq .skip (.seq (.assign 2 (.const initial))
     (.seq (.seq .tick (.seq
       (.loop (.bs (.ls ()) () .ln)
         (.seq (.assign 4 (.var 2))
           (.seq (.seq (.ite .notEqual 4 (.imm 0)
             (.seq (.seq .skip (.seq (.assign 4 (.op .sub [.var 2,.const 1]))
               (.seq (.seq (.assign 2 (.var 4)) .skip) .skip))) (.continue 0))
             (.break 0)) .tick) .skip)) (.ls ())) .tick))
       (.seq (.assign 4 (.const returned)) (.seq (.return 0 [4]) .skip)))))]


/-- Loop program before Word lowering, generated for the variable `x`. -/
def countdownLoopLiteral (initial returned : BitVec 64) : List (Nat × List Nat × HolLoopProg 64) :=
[(64, [],
    (HolLoopProg.skip.mark.seq ((HolLoopProg.call none (some 65) [] none).mark.seq HolLoopProg.skip.mark).mark).mark),
  (65, [],
    HolLoopProg.skip.mark.seq
      ((HolLoopProg.assign 1 (HolLoopExp.const initial)).mark.seq
        ((HolLoopProg.loop (Spt.ln.bn (Spt.ls PUnit.unit))
              ((HolLoopProg.assign 2 (HolLoopExp.var 1)).mark.seq
                  ((HolLoopProg.ite Cmp.notEqual 2 (RegImm.imm 0)
                            ((HolLoopProg.skip.mark.seq
                                      ((HolLoopProg.assign 2
                                                (HolLoopExp.op BinOp.sub
                                                  [HolLoopExp.var 1, HolLoopExp.const 1])).mark.seq
                                          (((HolLoopProg.assign 1 (HolLoopExp.var 2)).mark.seq
                                                    HolLoopProg.skip.mark).mark.seq
                                              HolLoopProg.skip.mark).mark).mark).mark.seq
                                (HolLoopProg.continue 0).mark).mark
                            (HolLoopProg.break 0).mark (Spt.ln.bn (Spt.ls PUnit.unit))).mark.seq
                      HolLoopProg.skip.mark).mark).mark
              Spt.ln).seq
          ((HolLoopProg.assign 2 (HolLoopExp.const returned)).mark.seq
              ((HolLoopProg.return [2]).mark.seq HolLoopProg.skip.mark).mark).mark)))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Lowering the countdown Loop literal to Word is independent of the initial
word. This is the actual Loop-to-Word compiler, with the generated contexts. -/
theorem countdownLoopLiteral_toWord (initial returned : BitVec 64) :
    loopToWordCompileHOL (countdownLoopLiteral initial returned) = countdownWordLiteral initial returned := by
  simp only [loopToWordCompileHOL, loopToWordCompileProgHOL, loopToWordCompFuncHOL,
    countdownLoopLiteral, countdownWordLiteral, List.map_cons, List.map_nil, List.length,
    Nat.zero_add, List.nil_append, LoopToWord.compHOL, LoopToWord.compExpHOL, accVarsHOL]
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The original Crep-to-Loop compiler emits the exact countdown Loop program. -/
theorem countdownLoopLiteral_zero_eq :
    let body : ProgHOL 64 := .dec (ofString "x") .one (.const (0 : BitVec 64))
      (.seq (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64))))
    compileProgHOLExact riscvConfig.isa
      (compileProgDeclsHOLW (compileTopExactHOL (singleEntryProgram (ofString "main") body) (ofString "main"))) =
    countdownLoopLiteral (0 : BitVec 64) (0 : BitVec 64) := by
  dsimp only
  rw [← compileProgWithStructuralLive_eq _ _ (countdown_crep_shapes (ofString "x") (0 : BitVec 64) (0 : BitVec 64))]
  simp only [compileProgDeclsHOLW,singleEntry_inline_selection_empty,CrepInlineRoute.compileInlTopHOLExact_nil]
  simp only [singleEntry_compileTop,singleEntry_main_freshName]
  unfold countdownLoopLiteral
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The original Pancake frontend emits exactly this Word program for the
zero-count example. -/
theorem countdownWordLiteral_zero_eq :
    panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64))))))) = countdownWordLiteral (0 : BitVec 64) (0 : BitVec 64) := by
  rw [singleEntry_countdown_panToWord, countdownLoopLiteral_zero_eq]
  exact countdownLoopLiteral_toWord 0 0

/-- The exact sequence of Word passes before register allocation. -/
def countdownPreAllocation (arity : Nat) (prog : WordLangProgHOL (BitVec 64)) :
    WordLangProgHOL (BitVec 64) :=
  let prog := WordSimp.compileExp prog
  let prog := WordInst.instSelectExecutable riscvConfig (maxVarHOL prog + 1) prog
  let prog := WordAlloc.fullSsaCcTrans arity prog
  let prog := WordAlloc.removeDeadProg prog
  let prog := WordCse.wordCommonSubexpElim prog
  let prog := WordCopy.copyProp prog
  let prog := WordInst.threeToTwoRegProg riscvConfig.twoRegArith prog
  let prog := WordUnreach.removeUnreach prog
  WordAlloc.removeDeadProg prog

/-- The checked allocator guard on one original pre-allocation Word function. -/
def countdownAllocatorGuard (row : Nat × Nat × WordLangProgHOL (BitVec 64)) : Bool :=
  let (name,arity,prog) := row
  let prog := countdownPreAllocation arity prog
  let tree := WordAlloc.getClashTree prog []
  let costs := (WordAlloc.getHeuristics 3 name prog).2
  let forced := WordAlloc.getForced riscvConfig prog []
  let stack := WordAlloc.getStackOnly prog
  Flapjack.RegAlloc.nativeRegAllocInputGuard costs tree forced stack

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual zero-count loop function passes every input guard of the
checked executable graph allocator. -/
theorem countdown_zero_allocator_guard :
    ((panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64)))))))).drop 1).map countdownAllocatorGuard = [true] := by
  rw [countdownWordLiteral_zero_eq]
  with_unfolding_all rfl

end SteppedFlapjack.PanToCrepSteps
