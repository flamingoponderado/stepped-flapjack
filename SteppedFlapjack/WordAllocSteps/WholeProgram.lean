import SteppedFlapjack.WordAllocSteps.StackReady
import Flapjack.Compiler.Backend.WordToWord.ExecutableCompile

/-! Connect the proven single-function pipeline to the whole Word compiler. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordToStackSteps
open Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width]

private theorem zip_member_of_left {α β : Type} (xs : List α) (ys : List β)
    (lengths : xs.length = ys.length) {x : α} (member : x ∈ xs) :
    ∃ y, (x,y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons a xs ih =>
    cases ys with
    | nil => simp at lengths
    | cons b ys =>
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨b,by simp⟩
      · obtain ⟨y,hy⟩ := ih ys lengths member
        exact ⟨y,by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hy⟩

private theorem zipped_compile_names (ac : AsmConfigExact width) (wc : Config)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (oracles : List (Option (Spt Nat))) (lengths : oracles.length = programs.length) :
    ((programs.zip oracles).map (fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac)).map Prod.fst = programs.map Prod.fst := by
  induction programs generalizing oracles with
  | nil => cases oracles <;> simp_all
  | cons p ps ih =>
    cases oracles with
    | nil => simp at lengths
    | cons col cols =>
      have tailLength : cols.length = ps.length := by simpa using lengths
      have h := ih cols tailLength
      simpa [fullCompileSingle,compileSingle] using congrArg (List.cons p.1) h

/-- The whole Word compiler preserves function names without additional guards. -/
theorem wholeCompile_names (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    (compile wc ac programs).2.map Prod.fst = programs.map Prod.fst := by
  exact zipped_compile_names ac wc programs _ (compile_zip_length wc programs)

/-- Every source function occurs in the actual whole-program Word output with
its corresponding oracle entry. This includes short-oracle fallback. -/
theorem wholeCompile_contains_single (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs) :
    ∃ col, (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,count,p),col)) ∈ (compile wc ac programs).2 := by
  obtain ⟨col,hcol⟩ := zip_member_of_left programs (nextNOracle programs.length wc.colOracle).1
    (compile_zip_length wc programs).symm member
  refine ⟨col,?_⟩
  change fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
    ((name,count,p),col) ∈ ((programs.zip (nextNOracle programs.length wc.colOracle).1).map
      (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac))
  exact List.mem_map.mpr ⟨_,hcol,rfl⟩

/-- The same membership holds for the executable implementation. -/
theorem wholeCompileExecutable_contains_single (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs) :
    ∃ col, (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,count,p),col)) ∈ (compileExecutable wc ac programs).2 := by
  rw [compileExecutable_eq]
  exact wholeCompile_contains_single wc ac programs name count p member

/-- For a supported function, the actual whole-program output contains a body
satisfying the proved Word-to-Stack structural and allocation conventions. -/
theorem wholeCompile_contains_stackReady (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (shape : LoopSequence p) :
    ∃ col q, (name,count,q) ∈ (compile wc ac programs).2 ∧
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
        ((name,count,p),col)).2.2 ∧
      LoopBlock q ∧ noInstallSubprogsHOL q = true ∧ flatExpConventions q = true ∧
      postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) q = true := by
  obtain ⟨col,hcol⟩ := wholeCompile_contains_single wc ac programs name count p member
  have eq : fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,count,p),col) = (name,count,(fullCompileSingle ac.twoRegArith
        (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2) := by
    simp [fullCompileSingle,compileSingle]
  rw [eq] at hcol
  exact ⟨col,_,hcol,rfl,fullCompileSingle_stackReady ac ac.twoRegArith count name wc.regAlg
    (ac.regCount-(5+ac.avoidRegs.length)) col shape⟩

/-- Every function produced by the whole Word compiler satisfies the Stack
compiler’s flat-expression and post-allocation conventions. -/
theorem wholeCompile_conventions (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    ∀ entry ∈ (compile wc ac programs).2,
      flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) entry.2.2 = true := by
  intro entry member
  change entry ∈ ((programs.zip (nextNOracle programs.length wc.colOracle).1).map
    (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac)) at member
  obtain ⟨⟨⟨name,count,p⟩,col⟩,_,rfl⟩ := List.mem_map.mp member
  exact fullCompileSingle_stackConventions ac ac.twoRegArith count name wc.regAlg
    (ac.regCount-(5+ac.avoidRegs.length)) p col

/-- A non-error source function run has a corresponding run of its actual
whole-program-compiled body, with a source-limit-dependent visit bound. -/
theorem wholeCompile_sourceBound {C F : Type} (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (shape : LoopSequence p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ col q selectedLocals targetPost,
      (name,count,q) ∈ (compile wc ac programs).2 ∧
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
        ((name,count,p),col)).2.2 ∧
      evaluate q {s with locals := locals,clock := limit} = (res,targetPost) ∧
      wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} targetPost ∧
      steps q {s with locals := locals,clock := limit} ≤ sizeOf q * (limit+1) := by
  obtain ⟨col,q,memberOut,qDef,_,_,_,_⟩ := wholeCompile_contains_stackReady wc ac programs name count p member shape
  obtain ⟨selectedLocals,targetPost,targetRun,rel,bound⟩ := compilerPrefix_alloc_correct
    ac ac.twoRegArith count name wc.regAlg (ac.regCount-(5+ac.avoidRegs.length)) col shape
    s post res locals limit run nonerror notTimeout sourceBound gc localRel domain
  rw [fullCompileSingle_eq_alloc ac ac.twoRegArith count name wc.regAlg
    (ac.regCount-(5+ac.avoidRegs.length)) col shape] at qDef
  subst q
  refine ⟨col,_,selectedLocals,targetPost,memberOut,?_,targetRun,rel,bound⟩
  rw [fullCompileSingle_eq_alloc ac ac.twoRegArith count name wc.regAlg
    (ac.regCount-(5+ac.avoidRegs.length)) col shape]

end SteppedFlapjack.WordAllocSteps
