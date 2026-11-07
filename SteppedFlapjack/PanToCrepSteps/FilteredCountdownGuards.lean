import SteppedFlapjack.PanToCrepSteps.CountdownCompiledLab
import Flapjack.Compiler.Backend.LabToTarget.FilterSkipSafety
import Flapjack.Compiler.Backend.LabToTarget.SkipFilterPreconditions
import Flapjack.Compiler.Backend.LabFilter.Proofs.SectionEnd

/-! Derive filtered countdown code guards from the real Lab compiler output. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Backend.LabFilter Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Misc
open SteppedFlapjack.LoopToWordSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Skip filtering preserves each of the actual Lab code-safety conditions. -/
theorem goodCode_filterSkip {width : Nat} [NeZero width] {G : Type}
    (config : AsmConfigExact width) (labels : Spt (Spt G)) (code : LabProgHOL width)
    (good : goodCode config labels code) : goodCode config labels (filterSkip code) := by
  obtain ⟨hend,hsec,hdistinct,hlabels,hdisjoint,htargets,hpre⟩ := good
  refine ⟨LabFilter.Proofs.secEndsWithLabelFilterSkip code hend,?_,?_,?_,?_,?_,allEncOkPreFilterSkip code config hpre⟩
  · intro sec hmem line hline
    rw [filterSkipMap] at hmem
    obtain ⟨original,horiginal,rfl⟩ := List.mem_map.mp hmem
    exact hsec original horiginal line (List.mem_filter.mp hline).1
  · simpa only [mapSectionNumFilterSkip] using hdistinct
  · intro sec hmem
    have hm : LabelSets.extractLabels sec.lines ∈ (filterSkip code).map (fun sectionData => LabelSets.extractLabels sectionData.lines) :=
      List.mem_map.mpr ⟨sec,hmem,rfl⟩
    rw [filterSkipExtractLabels] at hm
    obtain ⟨original,horiginal,heq⟩ := List.mem_map.mp hm
    rw [← heq]
    exact hlabels original horiginal
  · simpa only [mapSectionNumFilterSkip] using hdisjoint
  · simpa only [getLabelsFilterSkip,getCodeLabelsFilterSkip] using htargets

/-- Actual compilation supplies the filtered label, FFI, code-safety and
oracle guards. Machine memory, MMIO and code-buffer placement remain explicit. -/
theorem countdown_filteredLab_guards
    (name : MlString) (initial returned : BitVec 64) (config : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool) (cbspace : Nat)
    (bytes : List (BitVec 8)) (final : LabToTarget.Config)
    (target : mc.target = riscvTarget) (hcfg : backendConfigOk riscvConfig config)
    (ptr : mc.ptrReg = 10) (len : mc.lenReg = 11) (ptr2 : mc.ptr2Reg = 12) (len2 : mc.len2Reg = 13)
    (hcompile : LabToTarget.compile riscvConfig config.labConf
      (countdownStackLabCode name initial returned config) = some (bytes,final))
    (hprovided : ∀ ffis, config.labConf.ffiNames = some ffis →
      ∀ n ∈ ffis, ∃ s, n = HolFfiName.extCall s)
    (hffi : final.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc ms bytes cbspace t m dm sdm)
    (hentries : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      (final.shmemExtra.map (fun r => { r with
        entryPc := (mc.target.getPc ms).toNat+r.entryPc,
        exitPc := (mc.target.getPc ms).toNat+r.exitPc })).map ShmemInfoNum.entryPc =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      mc.mmioInfo = List.zip ((List.range final.shmemExtra.length).map (fun index => index+i))
        (final.shmemExtra.map (fun r => (r.nbytes,HolAddr.addr r.addrReg (BitVec.ofNat 64 r.addrOff),
          r.reg,BitVec.ofNat 64 ((mc.target.getPc ms).toNat+r.exitPc)))))
    (hbuffer : ∀ i, mmioPcsMinIndex mc.ffiNames = some i → ∀ bn, bn < cbspace →
      BitVec.ofNat 64 bn + BitVec.ofNat 64 bytes.length + mc.target.getPc ms ∉ mc.ffiEntryPcs.take i) :
    ∃ (i : Nat) (code2 : LabProgHOL 64) (labs : Spt (Spt Nat)),
      bytes = progToBytes code2 ∧
      LabMachineInitGuards mc ms (filterSkip (countdownStackLabCode name initial returned config))
        code2 labs config.labConf.initClock i cbspace t m dm sdm
        (fun n => ((countdownStackLabOracle config final n).1,
          filterSkip (countdownStackLabOracle config final n).2))
        (getShmemInfo code2 0 [] []).1 (getShmemInfo code2 0 [] []).2
        ((getShmemInfo code2 0 [] []).2.map (fun r => { r with
          entryPc := (mc.target.getPc ms).toNat+r.entryPc,
          exitPc := (mc.target.getPc ms).toNat+r.exitPc })) := by
  obtain ⟨i,code2,labs,hindex,hsubset,_,hremove,hbytes,hlab,hpos,hdrop,hinfo⟩ :=
    countdown_labCompilation_ffi name initial returned config hcfg bytes final mc.ffiNames hcompile hprovided hffi
  have codeGood := countdown_compiled_goodCode name initial returned config mc target hcfg
  have good : goodCode mc.target.config (.ln : Spt (Spt Nat))
      (filterSkip (countdownStackLabCode name initial returned config)) := by
    apply goodCode_filterSkip
    simpa only [target,riscvTarget,countdownStackLabCode] using codeGood
  have subset : listSubset ((findFfiNames (filterSkip (countdownStackLabCode name initial returned config))).filter
      (fun x => match x with | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true := by
    simp only [listSubset,List.all_eq_true,decide_eq_true_eq] at hsubset ⊢
    intro n hn
    exact hsubset n (List.mem_filter.mp hn).1
  have noinstall := countdown_compiled_noInstall name initial returned config.wordToWordConf config.stackConf config.dataConf
    (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset mc.ffiNames
  refine ⟨i,code2,labs,hbytes,good,riscvTarget_mcConfOk mc target ptr len ptr2 len2,?_,subset,?_,?_,?_,rfl,hdrop,hindex,?_,?_,?_,?_⟩
  · intro _
    have empty := emptyLabCompilerOracleOk final labs (progToBytes code2).length riscvConfig mc.ffiNames
      hlab (by simpa only [hbytes] using hpos) hffi
    simpa [countdownStackLabOracle,StackToLab.compileNoStubs,StackNames.compileHOL,filterSkip,target,riscvTarget] using empty
  · simpa only [target,riscvTarget] using hremove
  · simpa only [← hbytes] using hinit
  · exact Prod.mk.eta.symm
  · simpa only [hinfo] using hentries i hindex
  · simpa only [hinfo,List.length_map,List.map_map,Function.comp_def] using hmmio i hindex
  · apply noInstallOrNoShareMemFilterSkip
    simpa only [countdownStackLabCode,countdownNativeRiscV] using noinstall
  · simpa only [← hbytes] using hbuffer i hindex

set_option maxHeartbeats 1000000 in
theorem countdown_compiled_filtered_context {σ : Type}
    (name : MlString) (initial returned : BitVec 64) (config : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ) (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool) (cbspace : Nat)
    (bytes : List (BitVec 8)) (final : LabToTarget.Config)
    (target : mc.target = riscvTarget) (hcfg : backendConfigOk riscvConfig config)
    (ptr : mc.ptrReg = 10) (len : mc.lenReg = 11) (ptr2 : mc.ptr2Reg = 12) (len2 : mc.len2Reg = 13)
    (hcompile : LabToTarget.compile riscvConfig config.labConf
      (countdownStackLabCode name initial returned config) = some (bytes,final))
    (hprovided : ∀ ffis, config.labConf.ffiNames = some ffis →
      ∀ n ∈ ffis, ∃ s, n = HolFfiName.extCall s)
    (hffi : final.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc ms bytes cbspace t m dm sdm)
    (hentries : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      (final.shmemExtra.map (fun r => { r with
        entryPc := (mc.target.getPc ms).toNat+r.entryPc,
        exitPc := (mc.target.getPc ms).toNat+r.exitPc })).map ShmemInfoNum.entryPc =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      mc.mmioInfo = List.zip ((List.range final.shmemExtra.length).map (fun index => index+i))
        (final.shmemExtra.map (fun r => (r.nbytes,HolAddr.addr r.addrReg (BitVec.ofNat 64 r.addrOff),
          r.reg,BitVec.ofNat 64 ((mc.target.getPc ms).toNat+r.exitPc)))))
    (hbuffer : ∀ i, mmioPcsMinIndex mc.ffiNames = some i → ∀ bn, bn < cbspace →
      BitVec.ofNat 64 bn + BitVec.ofNat 64 bytes.length + mc.target.getPc ms ∉ mc.ffiEntryPcs.take i)
    (hmcInit : mcInitOk riscvConfig config mc)
    (bitmapPtr : BitVec 64) (bitmapsDomain sharedDomain : BitVec 64 → Bool) (dataSp labClock : Nat)
    (dmEq : dm = countdownStackLabDomain config t bitmapsDomain)
    (sdmEq : sdm = fun a => sharedDomain a && holByteAligned a)
    (layout : countdownStackMemoryLayout config mc ms t m bitmapPtr bitmapsDomain bytes cbspace dataSp
      (countdownNativeRiscV name initial returned config.wordToWordConf).1) :
    ∃ (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
      (backend : FullInitMachineContext stack),
      backend.mc = mc ∧ backend.machine = ms ∧ backend.lab.ffi = ffi ∧
      backend.lab.memory = m ∧ backend.lab.clock = labClock ∧
      backend.inputCode = (countdownNativeRiscV name initial returned config.wordToWordConf).2.2.2 ∧
      backend.bitmaps = (countdownNativeRiscV name initial returned config.wordToWordConf).1 ∧
      backend.coracle = (fun _ => (final,[],[])) := by
  obtain ⟨i,code2,labs,hbytes,guards⟩ := countdown_filteredLab_guards name initial returned config mc ms t m dm sdm
    cbspace bytes final target hcfg ptr len ptr2 len2 hcompile hprovided hffi hinit hentries hmmio hbuffer
  have stackInit := countdown_stackInit_from_memory name initial returned config mc ms ffi t m bitmapPtr bitmapsDomain sharedDomain
    bytes cbspace dataSp final (LabToTarget.compile mc.target.config) target hcfg hmcInit ptr len ptr2 len2 layout
  have stackInit' : Assumptions config.stackConf config.dataConf (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      (countdownNativeRiscV name initial returned config.wordToWordConf).1
      (countdownNativeRiscV name initial returned config.wordToWordConf).2.2.2
      (LabToTarget.makeInit mc ffi t m dm sdm ms (countdownStackLabCode name initial returned config)
        (LabToTarget.compile mc.target.config) (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length)
        cbspace (countdownStackLabOracle config final)) (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (final,[],[])) := by
    rw [dmEq,sdmEq]
    change Assumptions _ _ _ _ _ _ _ (LabToTarget.makeInit mc ffi t m
      (fun a => (decide (t.regs (StackNames.findNameSpt config.stackConf.regNames 2) ≤ a ∧
        a < t.regs (StackNames.findNameSpt config.stackConf.regNames 4)) || bitmapsDomain a) && holByteAligned a)
      (fun a => sharedDomain a && holByteAligned a) ms _ _ _ _ _) _ _ _
    rw [hbytes] at stackInit
    exact stackInit
  let backend := fullInitMachineContext_of_filteredLabInit config.stackConf config.dataConf
    (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1) (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
    riscvConfig.addrOffset (countdownNativeRiscV name initial returned config.wordToWordConf).1
    (countdownNativeRiscV name initial returned config.wordToWordConf).2.2.2
    (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (final,[],[])) mc ms ffi
    (countdownStackLabCode name initial returned config) code2 labs config.labConf.initClock i cbspace labClock t m dm sdm
    (countdownStackLabOracle config final) _ _ _ target guards stackInit'
  exact ⟨_,backend,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end SteppedFlapjack.PanToCrepSteps
