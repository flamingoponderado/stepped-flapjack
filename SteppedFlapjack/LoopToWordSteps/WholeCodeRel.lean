import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames
import Flapjack.Pancake.LoopToWord.Proofs.RelationsExact
import Flapjack.Pancake.CrepToLoop.StateRel

/-! The Loop-to-Word compiler constructs its own code relation. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopToWord Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Distinct parameter lists suffice for the actual Loop-to-Word output to be
related to its input code table, including first-match lookup behavior. -/
theorem wholeLoop_compiled_codeRel {width : Nat} [NeZero width]
    (programs : List (Nat × List Nat × HolLoopProg width))
    (paramsDistinct : ∀ name params body, (name,params,body) ∈ programs → params.Nodup) :
    loopToWordCodeRelHOLExact (sptFromAList programs) (sptFromAList (loopToWordCompileHOL programs)) := by
  intro name params body lookup
  have member : (name,params,body) ∈ programs := by
    rw [sptLookup_sptFromAList] at lookup
    exact sptAListLookup_mem name programs (params,body) lookup
  exact ⟨loopToWordLookupProgSomeLookupCompileProg programs name params body lookup,
    paramsDistinct name params body member⟩

/-- The Crep-to-Loop compiler generates a distinct range of parameter names
for every function, independently of the input parameter list. -/
theorem wholeCrepLoop_generated_params {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width)) :
    ∀ name params body, (name,params,body) ∈ compileProgHOLExact arch programs → params.Nodup := by
  have allDistinct : ((compileProgHOLExact arch programs).all (fun entry => entry.2.1.Nodup)) = true := by
    unfold compileProgHOLExact
    let comp := compFuncHOLExact (width := width) arch (crepToLoopMakeFuncsExactExecutable programs)
    have zipDistinct : ∀ (ns : List Nat) (entries : List (MlString × List Nat × CrepProgHOL width)),
        (List.zipWith (fun n entry => (n, List.range entry.2.1.length,
          optimiseHOL (comp entry.2.1 (crepSimpProgHOL entry.2.2)))) ns entries).all
          (fun entry => entry.2.1.Nodup) = true := by
      intro ns
      induction ns with
      | nil => intro; simp
      | cons n ns ih =>
        intro entries
        cases entries with
        | nil => simp
        | cons entry entries =>
          simp only [List.zipWith,List.all_cons,decide_eq_true List.nodup_range]
          exact ih entries
    exact zipDistinct _ programs
  intro name params body member
  have h := List.all_eq_true.mp allDistinct (name,params,body) member
  simpa using h

/-- The actual whole Crep-to-Loop and Loop-to-Word outputs satisfy the code
relation without an input-parameter distinctness premise. -/
theorem wholeCrepLoopWord_codeRel {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width)) :
    loopToWordCodeRelHOLExact (sptFromAList (compileProgHOLExact arch programs))
      (sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch programs))) := by
  exact wholeLoop_compiled_codeRel _ (wholeCrepLoop_generated_params arch programs)


/-- Replacing related states' code tables with the actual compiler outputs
preserves the complete Loop-to-Word state relation. -/
theorem wholeCrepLoopWord_stateRel_replaceCode {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width))
    (loop : LoopSemStateFiniteExact width F) (word : WordSemStateFiniteExact width C F)
    (related : loopToWordStateRelHOLExact loop word) :
    loopToWordStateRelHOLExact
      {loop with code := sptFromAList (compileProgHOLExact arch programs)}
      {word with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch programs))} := by
  obtain ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals,_⟩ := related
  exact ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals,wholeCrepLoopWord_codeRel arch programs⟩

end SteppedFlapjack.LoopToWordSteps
