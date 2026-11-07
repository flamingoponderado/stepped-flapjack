import SteppedFlapjack.PanToCrepSteps.CountdownStackInit
import Flapjack.Compiler.Backend.BackendProof.CompileLab
import Flapjack.Compiler.Backend.LabToTarget.FilterSkip
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabToTarget

/-! Facts about the actual Lab-to-target compilation of the countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabProps Flapjack.Misc

/-- Successful compilation determines the bytes, label table, final position,
and shared-memory metadata, including the compiler's skip filtering. -/
theorem countdown_labCompilation_facts
    (name : MlString) (initial returned : BitVec 64) (config : Backend.Config)
    (hcfg : backendConfigOk riscvConfig config)
    (bytes : List (BitVec 8)) (final : LabToTarget.Config)
    (hcompile : LabToTarget.compile riscvConfig config.labConf
      (countdownStackLabCode name initial returned config) = some (bytes,final)) :
    ∃ (ffis : List HolFfiName) (code2 : LabProgHOL 64) (labs : Spt (Spt Nat)),
      (config.labConf.ffiNames = some ffis ∨
        (config.labConf.ffiNames = none ∧
          ffis = findFfiNames (filterSkip (countdownStackLabCode name initial returned config)))) ∧
      listSubset (findFfiNames (filterSkip (countdownStackLabCode name initial returned config))) ffis = true ∧
      removeLabels config.labConf.initClock riscvConfig 0 .ln ffis
        (filterSkip (countdownStackLabCode name initial returned config)) = some (code2,labs) ∧
      bytes = progToBytes code2 ∧ final.labels = labs ∧ final.pos = bytes.length ∧
      final.ffiNames = some (ffis ++ (getShmemInfo code2 0 [] []).1) ∧
      final.shmemExtra = (getShmemInfo code2 0 [] []).2 := by
  have hpos : config.labConf.pos = 0 := hcfg.2.2.2.2.1
  have hlabs : config.labConf.labels = .ln := hcfg.2.2.2.2.2.1
  change compileLab riscvConfig config.labConf
    (filterSkip (countdownStackLabCode name initial returned config)) = some (bytes,final) at hcompile
  obtain ⟨ffis,hnone,code2,labs,hselected,hremove,hbytes,hfinal⟩ :=
    compileLab_some _ hcompile
  have hsubset : listSubset (findFfiNames (filterSkip (countdownStackLabCode name initial returned config))) ffis = true := by
    rcases hselected with hsome | hnone'
    · have hc := hcompile
      simp only [compileLab,hsome] at hc
      split at hc
      · assumption
      · contradiction
    · rw [hnone hnone']
      simp [listSubset]
  refine ⟨ffis,code2,labs,?_,hsubset,?_,hbytes,?_,?_,?_,?_⟩
  · rcases hselected with hsome | hnone'
    · exact Or.inl hsome
    · exact Or.inr ⟨hnone',hnone hnone'⟩
  · simpa only [hpos,hlabs] using hremove
  · simp only [hfinal]
  · simp only [hfinal,hpos,Nat.add_zero,hbytes]
  · simp only [hfinal,hpos]
  · simp only [hfinal,hpos]

/-- The FFI prefix used by actual compilation is exactly the external-call
prefix of the machine interface; the remaining names are generated MMIO calls. -/
theorem countdown_labCompilation_ffi
    (name : MlString) (initial returned : BitVec 64) (config : Backend.Config)
    (hcfg : backendConfigOk riscvConfig config)
    (bytes : List (BitVec 8)) (final : LabToTarget.Config) (machineFfis : List HolFfiName)
    (hcompile : LabToTarget.compile riscvConfig config.labConf
      (countdownStackLabCode name initial returned config) = some (bytes,final))
    (hprovided : ∀ ffis, config.labConf.ffiNames = some ffis →
      ∀ n ∈ ffis, ∃ s, n = HolFfiName.extCall s)
    (hffi : final.ffiNames = some machineFfis) :
    ∃ (i : Nat) (code2 : LabProgHOL 64) (labs : Spt (Spt Nat)),
      mmioPcsMinIndex machineFfis = some i ∧
      listSubset (findFfiNames (filterSkip (countdownStackLabCode name initial returned config))) (machineFfis.take i) = true ∧
      listSubset ((findFfiNames (countdownStackLabCode name initial returned config)).filter
        (fun x => match x with | .extCall _ => true | _ => false)) (machineFfis.take i) = true ∧
      removeLabels config.labConf.initClock riscvConfig 0 .ln (machineFfis.take i)
        (filterSkip (countdownStackLabCode name initial returned config)) = some (code2,labs) ∧
      bytes = progToBytes code2 ∧ final.labels = labs ∧ final.pos = bytes.length ∧
      machineFfis.drop i = (getShmemInfo code2 0 [] []).1 ∧
      final.shmemExtra = (getShmemInfo code2 0 [] []).2 := by
  obtain ⟨ffis,code2,labs,hselected,hsubset,hremove,hbytes,hlab,hpos,hnames,hinfo⟩ :=
    countdown_labCompilation_facts name initial returned config hcfg bytes final hcompile
  have hffis : ∀ n ∈ ffis, ∃ s, n = HolFfiName.extCall s := by
    rcases hselected with hs | ⟨_,rfl⟩
    · exact hprovided ffis hs
    · exact findFfiNamesEvery _ _ rfl
  let newNames := (getShmemInfo code2 0 [] []).1
  let info := (getShmemInfo code2 0 [] []).2
  have heq : getShmemInfo code2 0 [] [] = (newNames,info) := by
    exact Prod.mk.eta.symm
  have hnew : ∀ n ∈ newNames, ∀ s, n ≠ HolFfiName.extCall s := by
    obtain ⟨suffix,hsuffix,hshared⟩ := getShmemInfo_mappedNames code2 0 [] [] newNames info heq
    simp only [List.nil_append] at hsuffix
    rw [hsuffix]
    intro n hn s
    obtain ⟨op,rfl⟩ := hshared n hn
    intro h
    cases h
  have hmachine : machineFfis = ffis ++ newNames := by
    apply Option.some.inj
    exact hffi.symm.trans hnames
  have hindex : mmioPcsMinIndex machineFfis = some ffis.length := by
    rw [hmachine]
    exact mmioPcsMinIndex_append newNames ffis ⟨hnew,hffis⟩
  have htake : machineFfis.take ffis.length = ffis := by
    rw [hmachine,List.take_append_length]
  have hdrop : machineFfis.drop ffis.length = newNames := by
    rw [hmachine,List.drop_append_length]
  have hfiltered : listSubset ((findFfiNames (countdownStackLabCode name initial returned config)).filter
      (fun x => match x with | .extCall _ => true | _ => false)) ffis = true := by
    rw [← Flapjack.Compiler.Backend.LabToTarget.FilterSkip.findFfiNamesFilterSkip
      (countdownStackLabCode name initial returned config)]
    simp only [listSubset,List.all_eq_true,decide_eq_true_eq] at hsubset ⊢
    intro n hn
    exact hsubset n (List.mem_filter.mp hn).1
  exact ⟨ffis.length,code2,labs,hindex,by simpa only [htake] using hsubset,
    by simpa only [htake] using hfiltered,by simpa only [htake] using hremove,
    hbytes,hlab,hpos,hdrop,hinfo⟩

/-- The actual Lab compiler output supplies the no-install oracle contract. -/
theorem countdown_labCompilation_oracle
    (name : MlString) (initial returned : BitVec 64) (config : Backend.Config)
    (hcfg : backendConfigOk riscvConfig config)
    (bytes : List (BitVec 8)) (final : LabToTarget.Config) (machineFfis : List HolFfiName)
    (hcompile : LabToTarget.compile riscvConfig config.labConf
      (countdownStackLabCode name initial returned config) = some (bytes,final))
    (hffi : final.ffiNames = some machineFfis) :
    compilerOracleOk (countdownStackLabOracle config final) final.labels bytes.length riscvConfig machineFfis := by
  exact Flapjack.Pancake.Proofs.PanToTarget.panToTargetCompilerOracleOk
    riscvConfig config.labConf final (countdownStackLabCode name initial returned config)
    bytes machineFfis config.stackConf.regNames config.stackConf.jump riscvConfig.addrOffset
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) hcompile hcfg.2.2.2.2.1 hffi

end SteppedFlapjack.PanToCrepSteps
