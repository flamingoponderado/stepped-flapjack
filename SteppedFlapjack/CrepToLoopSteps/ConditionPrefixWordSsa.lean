import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.BackendReady
import SteppedFlapjack.CrepToLoopSteps.WordSimpSequence
import SteppedFlapjack.LoopToWordSteps.WordSsaSequence

/-! Crep sequences through the actual full SSA prefix. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopToWordSteps

/-- Completed Crep initialization, loop and continuation yield a semantically
related execution through Loop-to-Word, WordSimp, selection and full SSA, with
an actual SSA visit bound computed from the Crep source limit. -/
theorem branchConditionWhileBranch_wordSsa_bound {F C : Type}
    (ac : AsmConfigExact 64) (count : Nat)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (condition : CrepExpHOL 64) (shape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source sourcePost : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (loop : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 C F)
    (wordCtxt : Spt Nat) (labels : Nat × Nat) (locals : Spt (WordLocW 64)) (limit factor : Nat)
    (factorDef : factor = 1 + sizeOf (compileHOLExact ctxt live init) +
      (1 + (1 + sizeOf (compileHOLExact ctxt live (.while condition body))) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
          sizeOf (compileHOLExact ctxt live body)+3) + sizeOf (compileHOLExact ctxt live tail)))
    (complete : CompleteCrepResult result)
    (run : evalCrepSemHOLProgExact source (.seq init (.seq (.while condition body) tail)) = (result,sourcePost))
    (stepBound : CrepSteps.steps (.seq init (.seq (.while condition body) tail)) source ≤ limit)
    (stateRel : crepToLoopStateRelExact source loop)
    (memRel : crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals loop.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code loop.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals loop.locals)
    (loopWordRel : loopToWordStateRelHOLExact loop word)
    (loopLocalsRel : LoopToWord.localsRelHOL wordCtxt loop.locals word.locals)
    (retLookup : sptLookup 0 word.locals = some (.loc 1 0))
    (dim : goodDimindex 64) (retLabel : ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true)
    (loopVars : ∀ k, sptMem k (accVarsHOL (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) .ln) → sptMem k wordCtxt)
    (gc : gcFunConstOk word.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp
      (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1)+1))
      (compileExp (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp
      (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ extra loopPost wordPost wordResult selectedLocals targetPost,
      crepToLoopStateRelExact sourcePost loopPost ∧
      LoopToWord.CompileCorrect.resultCase wordCtxt (.loc 1 0) {word with clock := word.clock+extra}
        (resultToLoop result) loopPost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      Flapjack.WordAlloc.wordStateEqRel
        {wordPost with locals := selectedLocals,clock := 6*(factor*(limit+1))-((word.clock+extra)-wordPost.clock)} targetPost ∧
      WordSemStateFiniteExact.evaluate
        (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp
          (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1)+1)
          (compileExp (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1)))
          {word with locals := locals,clock := 6*(factor*(limit+1))} = (wordResult,targetPost) ∧
      WordSteps.steps
        (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp
          (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1)+1)
          (compileExp (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1)))
          {word with locals := locals,clock := 6*(factor*(limit+1))} ≤
        sizeOf (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp
          (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1)+1)
          (compileExp (LoopToWord.compHOL wordCtxt (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail))) labels).1))) *
            (6*(factor*(limit+1))+1) := by
  obtain ⟨extra,loopPost,loopRun,postRel,_,_,_,_,loopBound⟩ :=
    branchConditionWhileBranch_programBound init initShape condition shape body tail bodyShape tailShape ctxt live
      source sourcePost result loop run (completeCrep_nonerror complete) stateRel memRel globalsRel codeRel localsRel
  have shiftedRel : loopToWordStateRelHOLExact {loop with clock := loop.clock+extra} {word with clock := word.clock+extra} := by
    rcases loopWordRel with ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    refine ⟨len,hm,hd,hs,?_,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    simp only
    omega
  have loopComplete : CompleteLoopResult (resultToLoop result) := completeCrep_loop complete
  have loopNotError : resultToLoop result ≠ some .error := by cases complete <;> simp [resultToLoop]
  have bound : LoopSteps.steps (compileHOLExact ctxt live (.seq init (.seq (.while condition body) tail)))
      {loop with clock := loop.clock+extra} ≤ factor*(limit+1) := by
    rw [factorDef]
    exact Nat.le_trans loopBound (Nat.mul_le_mul_left _ (Nat.add_le_add_right stepBound 1))
  obtain ⟨wordPost,wordResult,selectedLocals,targetPost,wordResultRel,wordFfi,ssaRel,ssaRun,ssaBound⟩ :=
    loopSequence_wordSsa_bound ac count _
      (branchConditionWhileBranch_wordSimpShape init initShape condition shape body tail bodyShape tailShape ctxt live)
      {loop with clock := loop.clock+extra} loopPost (resultToLoop result) {word with clock := word.clock+extra}
      wordCtxt labels locals (factor*(limit+1))
      ⟨loopRun,loopNotError,shiftedRel,loopLocalsRel,retLookup,dim,retLabel,loopVars⟩ loopComplete
      (by simpa using gc) vars localRel domain bound
  refine ⟨extra,loopPost,wordPost,wordResult,selectedLocals,targetPost,postRel,wordResultRel,?_,ssaRel,ssaRun,ssaBound⟩
  have ffiRel : sourcePost.ffi = loopPost.ffi := postRel.2.2.2.2.1
  exact wordFfi.trans ffiRel.symm

end SteppedFlapjack.CrepToLoopSteps
