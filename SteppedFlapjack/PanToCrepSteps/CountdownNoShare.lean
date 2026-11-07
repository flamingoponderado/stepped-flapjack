import SteppedFlapjack.PanToCrepSteps.CountdownBitmapProof
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopTop
import Flapjack.Compiler.Backend.StackToLab.Proofs.NoShmemop
import SteppedFlapjack.PanToCrepSteps.FilteredCountdownGuards

/-! Shared-memory exclusion for the compiled countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

private theorem branch_noShare {width : Nat} [NeZero width] {p : WordLangProgHOL (BitVec width)}
    (h : Branch p) : noShareInstSubprogsHOL p = true := by
  induction h <;> simp_all [noShareInstSubprogsHOL,notCreatedSubprogsWithMemOp]

private theorem tail_noShare {width : Nat} [NeZero width] {p : WordLangProgHOL (BitVec width)}
    (h : RegTailShape p) : noShareInstSubprogsHOL p = true := by
  induction h with
  | branch h => exact branch_noShare h
  | call _ _ => rfl
  | seq _ _ ha hb =>
    simp only [noShareInstSubprogsHOL] at ha hb
    simp [noShareInstSubprogsHOL,notCreatedSubprogsWithMemOp,ha,hb]

private theorem loop_noShare {width : Nat} [NeZero width] {p : WordLangProgHOL (BitVec width)}
    (h : LoopSequence p) : noShareInstSubprogsHOL p = true := by
  induction h with
  | branch h => exact branch_noShare h
  | loop _ _ h => simpa [noShareInstSubprogsHOL,notCreatedSubprogsWithMemOp] using branch_noShare h
  | seq _ _ ha hb =>
    simp only [noShareInstSubprogsHOL] at ha hb
    simp [noShareInstSubprogsHOL,notCreatedSubprogsWithMemOp,ha,hb]

private theorem block_noShare {width : Nat} [NeZero width] {p : WordLangProgHOL (BitVec width)}
    (h : LoopBlock p) : noShareInstSubprogsHOL p = true := by
  induction h <;> simp_all [noShareInstSubprogsHOL,notCreatedSubprogsWithMemOp]

set_option maxHeartbeats 1000000 in
/-- The real countdown Lab program has no shared-memory instructions. -/
theorem countdown_lab_noShare (name : MlString) (initial returned : BitVec 64) :
    LabProps.noShareMemInst (countdownStackLabCode name initial returned countdownRiscVBackend) := by
  let source := singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
    (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
    (.return (.const returned)))))
  let word := panToWordCompileProgHOL Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa source
  let allocated := (WordToWord.compile countdownRiscVBackend.wordToWordConf
    Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig word).2
  have wordShapes : ∀ row ∈ word, SteppedFlapjack.LoopLiveSteps.WordTailEntryShape row.2.2 ∨ LoopSequence row.2.2 := by
    dsimp only [word,source]
    rw [singleEntry_countdown_panToWord]
    apply SteppedFlapjack.LoopToWordSteps.loopProgram_bitmapShapes
    apply SteppedFlapjack.CrepToLoopSteps.supportedProgram_loopShapes
    exact countdown_crep_shapes name initial returned
  have shapes := wholeCompile_tailOrLoop_shape countdownRiscVBackend.wordToWordConf
    Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig word wordShapes
  have guard : (allocated.all fun row => noShareInstSubprogsHOL row.2.2) = true := by
    rw [List.all_eq_true]
    intro row member
    have h := shapes row member
    rcases h with tail | loop | block
    · exact tail_noShare tail
    · exact loop_noShare loop
    · exact block_noShare block
  let native := compileNative Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig false allocated
  have safe := compileNoShmemop Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig allocated
    native.1 native.2.1 native.2.2.1 native.2.2.2 (by exact Prod.mk.eta.symm) guard
  apply StackToLab.Proofs.NoShmemop.compileNoShareMemInst
    native.2.2.2 (countdownStackLabCode name initial returned countdownRiscVBackend)
  constructor
  · intro row member
    exact List.all_eq_true.mp safe row member
  · rfl

set_option maxHeartbeats 4000000 in
/-- A successful Lab compilation has no shared-memory metadata; its FFI names
are exactly the external-call names in the compiled countdown code. -/
theorem countdown_lab_noSharedMetadata (name : MlString) (initial returned : BitVec 64)
    (bytes : List (BitVec 8)) (final : LabToTarget.Config)
    (hcompile : LabToTarget.compile riscvConfig countdownRiscVBackend.labConf
      (countdownStackLabCode name initial returned countdownRiscVBackend) = some (bytes,final)) :
    final.shmemExtra = [] ∧
    final.ffiNames = some (findFfiNames (countdownStackLabCode name initial returned countdownRiscVBackend)) := by
  obtain ⟨ffis,code2,labs,hselected,_,hremove,_,_,_,hnames,hinfo⟩ :=
    countdown_labCompilation_facts name initial returned countdownRiscVBackend riscvPancakeBackendConfigOk bytes final hcompile
  have selected : ffis = findFfiNames (filterSkip (countdownStackLabCode name initial returned countdownRiscVBackend)) := by
    rcases hselected with h | ⟨_,eq⟩
    · change none = some ffis at h
      cases h
    · exact eq
  have good0 := countdown_compiled_goodCode name initial returned countdownRiscVBackend countdownMachineConfig rfl riscvPancakeBackendConfigOk
  have good := goodCode_filterSkip riscvConfig (.ln : Spt (Spt Nat)) _ good0
  obtain ⟨ends,labels,ids,distinct,disjoint,targets,pre⟩ := good
  have mcok := riscvTarget_mcConfOk countdownMachineConfig rfl rfl rfl rfl rfl
  have result := removeLabels_correct countdownRiscVBackend.labConf.initClock riscvConfig 0 .ln ffis
    (filterSkip (countdownStackLabCode name initial returned countdownRiscVBackend)) code2 labs
    ⟨hremove,mcok.2.2.2.2.2.2.2,ends,labels,ids,distinct,disjoint,targets,pre,by decide,
      by simp [labLookup,sptLookup]⟩
  have similar := result.2.1
  have noShare := (noShareMemFilterSkip _).2 (countdown_lab_noShare name initial returned)
  have noShare2 := codeSimilar_noShareMem _ _ ⟨similar,noShare⟩
  have info := noShareMem_getShmemInfo code2 0 [] [] noShare2
  constructor
  · rw [info] at hinfo
    exact hinfo
  · rw [info] at hnames
    simp only [List.append_nil] at hnames
    rw [selected,findFfiNamesFilterSkip] at hnames
    exact hnames

set_option maxHeartbeats 1000000 in
/-- Successful full countdown compilation emits no shared-memory interface
entries, independently of its external-call interface. -/
theorem countdown_artifact_noSharedMetadata (name : MlString) (initial returned : BitVec 64)
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (final : Backend.Config)
    (hcompile : Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = some (bytes,bitmaps,final)) :
    final.labConf.shmemExtra = [] ∧
    final.labConf.ffiNames = some (findFfiNames (countdownStackLabCode name initial returned countdownRiscVBackend)) := by
  let source := singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
    (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
    (.return (.const returned)))))
  let full := Flapjack.Pancake.Proofs.PanToTarget.compileProgMaxAsmExecutable countdownRiscVBackend riscvConfig source
  have artifact : full.1 = some (bytes,bitmaps,final) := by
    simpa only [full,source,Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast_eq_fst] using hcompile
  have hfull : full = (some (bytes,bitmaps,final),full.2) := Prod.ext artifact rfl
  have hlab := (countdown_executableCompiler_lab name initial returned countdownMachineConfig rfl
    bytes bitmaps final full.2 (by simpa only [full,source] using hfull)).1
  exact countdown_lab_noSharedMetadata name initial returned bytes final.labConf hlab

end SteppedFlapjack.PanToCrepSteps
