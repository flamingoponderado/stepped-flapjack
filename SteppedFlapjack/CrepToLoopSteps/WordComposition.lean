import SteppedFlapjack.CrepToLoopSteps.Sequence

/-! Compose direct Crep-to-Loop step preservation with Loop-to-Word. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A direct Crep run produces an actual Word run within twice its Crep
statement count. Both compiler passes and the intermediate execution are
explicit, and the extra source clock is carried through to Word. -/
theorem directProgram_word_bound {width : Nat} [NeZero width] {C F : Type}
    (p : CrepProgHOL width) (shape : DirectProgram p)
    (source sourcePost : CrepSemHOLState width F) (result : Option (CrepResultHOLExact width))
    (loop : LoopSemStateFiniteExact width F) (word : WordSemStateFiniteExact width C F)
    (crepCtxt : CrepToLoopContextExact) (live : NumSet) (wordCtxt : Spt Nat)
    (retv : WordLocW width) (labels : Nat × Nat)
    (run : evalCrepSemHOLProgExact source p = (result,sourcePost))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source loop)
    (memRel : crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals loop.globals)
    (codeRel : crepToLoopCodeRelExact crepCtxt source.code loop.code)
    (localsRel : crepToLoopLocalsRelExact crepCtxt live source.locals loop.locals)
    (loopWordRel : loopToWordStateRelHOLExact loop word)
    (wordLocalsRel : LoopToWord.localsRelHOL wordCtxt loop.locals word.locals)
    (retLookup : sptLookup 0 word.locals = some retv)
    (dim : goodDimindex width) (retLabel : ¬ wordSemIsWordLoc retv = true)
    (vars : ∀ k, sptMem k (accVarsHOL (compileHOLExact crepCtxt live p) .ln) → sptMem k wordCtxt) :
    ∃ extra loopResult loopPost wordResult wordPost,
      evaluate (compileHOLExact crepCtxt live p) {loop with clock := loop.clock + extra} =
        (loopResult,loopPost) ∧ loopResult = resultToLoop result ∧
      crepToLoopStateRelExact sourcePost loopPost ∧
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL wordCtxt (compileHOLExact crepCtxt live p) labels).1
        {word with clock := word.clock + extra} = (wordResult,wordPost) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase wordCtxt retv {word with clock := word.clock + extra}
        loopResult loopPost wordResult wordPost ∧
      WordSteps.steps (LoopToWord.compHOL wordCtxt (compileHOLExact crepCtxt live p) labels).1
        {word with clock := word.clock + extra} ≤ 2 * CrepSteps.steps p source := by
  obtain ⟨extra,loopResult,loopPost,loopRun,loopPostRel,_,_,_,loopResultMap,_,loopBound⟩ :=
    directProgram_correct_with_steps shape source result sourcePost loop crepCtxt live run nonerror
      stateRel memRel globalsRel codeRel (by trivial) localsRel
  have loopNonerror : loopResult ≠ some .error := by
    rw [loopResultMap]
    cases result with
    | none => simp [resultToLoop]
    | some r => cases r <;> simp_all [resultToLoop]
  have shiftedRel : loopToWordStateRelHOLExact {loop with clock := loop.clock + extra}
      {word with clock := word.clock + extra} := by
    rcases loopWordRel with ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    refine ⟨len,hm,hd,hs,?_,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    simp only
    omega
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordResultRel,wordBound⟩ :=
    LoopToWordSteps.directProgram_correct_with_steps (compile_directProgram shape crepCtxt live)
      {loop with clock := loop.clock + extra} loopResult loopPost {word with clock := word.clock + extra}
      wordCtxt retv labels ⟨loopRun,loopNonerror,shiftedRel,wordLocalsRel,retLookup,dim,retLabel,vars⟩
  refine ⟨extra,loopResult,loopPost,wordResult,wordPost,loopRun,loopResultMap,loopPostRel,
    wordRun,?_,wordResultRel,Nat.le_trans wordBound loopBound⟩
  have ffiRel : sourcePost.ffi = loopPost.ffi := loopPostRel.2.2.2.2.1
  exact wordFfi.trans ffiRel.symm

end SteppedFlapjack.CrepToLoopSteps
