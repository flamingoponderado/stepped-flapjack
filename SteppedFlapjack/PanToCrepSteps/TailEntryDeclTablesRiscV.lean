import SteppedFlapjack.CrepToLoopSteps.TailRiscVComposition
import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.PanToCrepSteps.TailEntryFrontendRiscV
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations
import SteppedFlapjack.PanToCrepSteps.TailEntryDeclCompiledRiscV
import SteppedFlapjack.CrepToLoopSteps.WholeInitialRelations
import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas

/-! Crep-to-RISC-V composition for a branch entry calling an initialized loop. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack.Basis.Pure.MlString Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps


open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Derive frontend code relations from actual compiler tables before the machine bound. -/
theorem panTailDeclEntry_frontendTables_riscvWithin {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (source : CrepSemHOLState 64 F)
    (target : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (crepRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (arch : AsmArchitecture) (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (entryName : MlString) (entryBody : CrepProgHOL 64)
    (unique : (crepPrograms.map Prod.fst).Nodup)
    (entryLookup : holAlookup crepPrograms entryName = some ([],entryBody))
    (programShapes : ∀ n ps p, (n,ps,p) ∈ crepPrograms → SupportedCodeBody p)
    (ctxtEq : ctxt = mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable crepPrograms) 0)
    (sourceCodeEq : source.code = alistToFmapCodeExact crepPrograms)
    (loopCodeEq : target.code = sptFromAList (compileProgHOLExact arch crepPrograms))
    (wordCodeEq : word.code = sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)))
    (wordData : LoopWordDataRel target word)
    (panLocal : MlS) (panInitializer : ExpHOL 64)
    (panInit panCalleeInit : ProgHOL 64) (panCondition : ExpHOL 64) (panBody panTail : ProgHOL 64)
    (callerContext : PanToCrepContextExact 64)
    (sourceInitShape : PanToCrepSteps.BranchProgram callerContext panInit)
    (panInitializerShape : ScalarExpression (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panInitializer)
    (panInitShape : PanToCrepSteps.BranchProgram (scalarDeclContext (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panLocal) panCalleeInit)
    (panConditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panLocal) panCondition)
    (panBodyShape : PanToCrepSteps.BranchProgram (scalarDeclContext (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panLocal) panBody)
    (panTailShape : PanToCrepSteps.BranchProgram (scalarDeclContext (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panLocal) panTail)
    (pan panMiddle panPost : PanSemStateFiniteExact 64 F) (panResult : Option (PanSemResultExact 64))
    (panLocals : HolFiniteMapExact MlString (ValueHOL 64)) (panReturnShape : ShapeHOL)
    (panInitRun : pan.evaluateHOLFiniteState panInit = (none,panMiddle))
    (panLookup : lookupCodeHOLFinite panMiddle.code.lookup name [] =
      some (.dec panLocal .one panInitializer (.seq panCalleeInit (.seq (.while panCondition panBody) panTail)),panLocals,panReturnShape))
    (panClock : panMiddle.clock ≠ 0)
    (panRun : (callEntryStateHOLFinite panMiddle panLocals).evaluateHOLFiniteState
      (.dec panLocal .one panInitializer (.seq panCalleeInit (.seq (.while panCondition panBody) panTail))) = (panResult,panPost))
    (panComplete : CompletePanResult panResult)
    (initLocalised : localisedProgHOL panInit = true)
    (initialPanRel : panToCrepStateRelFiniteExact pan source)
    (initialCodeRel : codeRelExactHOLW callerContext pan.code source.code)
    (initialExcpRel : panToCrepExcpRelFiniteExact callerContext.eids pan.eshapes)
    (initialLocalsRel : panToCrepLocalsRelFiniteExact callerContext pan.locals source.locals)
    (panBound : globalEntrySteps panInit name [] pan ≤ limit) :
    TailProgramShapes (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) ∧
    ∃ (value condition : CrepExpHOL 64),
    compileExpExactHOLW (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panInitializer = ([value],.one) ∧
    compileExpExactHOLW (scalarDeclContext (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panLocal) panCondition = ([condition],.one) ∧
    let panContext := ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []
    let init := compileProgExactHOLW callerContext panInit
    let inner := scalarDeclContext panContext panLocal
    let calleeInit := compileProgExactHOLW inner panCalleeInit
    let body := compileProgExactHOLW inner panBody
    let tail := compileProgExactHOLW inner panTail
    let loopEntry := optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))
    let loopLimit := branchTailDeclLoopLimit ctxt live name init (panContext.vmax+1) value calleeInit condition body tail
      (sizeOf init + 2 + (4 + sizeOf (compileProgExactHOLW inner panCalleeInit) +
        sizeOf (compileProgExactHOLW inner panBody) + sizeOf (compileProgExactHOLW inner panTail)) * limit)
    ∃ (post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64)),
    panToCrepStateRelFiniteExact panPost post ∧
    pcCompileCorrectResultRel panContext panPost post panResult result ∧
    ∃ extra loopPost, crepToLoopStateRelExact post loopPost ∧
    let shiftedWord := {word with clock := word.clock+extra}
    ∀ (ac : AsmConfigExact 64) (count entryName alg regCount : Nat) (col : Option (Spt Nat))
      (wordCtxt : Spt Nat) (labels : Nat × Nat)
      (compiledCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (locals : Spt (WordLocW 64))
      (_wordLocals : LoopToWord.localsRelHOL wordCtxt target.locals word.locals)
      (_retLookup : sptLookup 0 word.locals = some (.loc 1 0))
      (_dim : goodDimindex 64) (_retLabel : ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true)
      (_vars : ∀ k, sptMem k (accVarsHOL loopEntry .ln) → sptMem k wordCtxt)
      (_gc : gcFunConstOk word.gcFun)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (_programsEq : programs = loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))
    (_entryMember : (entryName,count,(LoopToWord.compHOL wordCtxt loopEntry labels).1) ∈ programs)
    (_algorithm : alg = wc.regAlg) (_registers : regCount = ac.regCount-(5+ac.avoidRegs.length))
    (_colour : col = entryColour wc programs entryName)
    (_wordCode : shiftedWord.code = sptFromAList programs)
    (_compiledCodeEq : compiledCode = sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2)
    (_localsRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL wordCtxt loopEntry labels).1)+1) shiftedWord.locals locals)
    (_domain : sptDomain locals = (fun key => key ∈ evenList count))
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F) (frameSize frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64) (start argumentCount : Nat)
    (_stackRel : stateRel ac regCount frameSize frame
      {shiftedWord with code := compiledCode,locals := locals,clock := tailWordReplayLimit loopEntry wordCtxt labels compiledCode loopLimit}
      {entry with stackSpace := entry.stackSpace-(frameSize-(argumentCount-regCount))} lens 0)
    (_native : Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((entryName,count,(LoopToWord.compHOL wordCtxt loopEntry labels).1),col)).2.2
      (bs,n) (regCount,frameSize,frame) = (compiled,(bsPost,nPost)))
    (_lengthBound : (appListAppend bs).length ≤ n) (_bitmapBound : n-(appListAppend bs).length ≤ entry.bitmaps.length)
    (_bitmapPrefix : List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n-(appListAppend bs).length)))
    (_labelCheck : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc)
    (_maxBound : maxVarHOL (fullCompileSingle ac.twoRegArith regCount alg ac ((entryName,count,(LoopToWord.compHOL wordCtxt loopEntry labels).1),col)).2.2 < 2*frame+2*regCount)
    (_frameDef : frame = max (maxVarHOL (fullCompileSingle ac.twoRegArith regCount alg ac ((entryName,count,(LoopToWord.compHOL wordCtxt loopEntry labels).1),col)).2.2 / 2 + 1 - regCount) (argumentCount-regCount))
    (_frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (_space : frameSize-(argumentCount-regCount) ≤ entry.stackSpace)
    (_found : sptLookup start entry.code = some (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((entryName,count,(LoopToWord.compHOL wordCtxt loopEntry labels).1),col)).2.2 argumentCount regCount (bs,n)).1)
    (inputCode : List (Nat × HolProg 64)) (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat) (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat)
    (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F) (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (_distinct : (inputCode.map Prod.fst).Nodup) (_sourceCode : entry.code = sptFromAList inputCode)
    (_pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := tailStackReplayLimit ac count entryName alg regCount col loopEntry wordCtxt labels compiledCode loopLimit+1} entry.regs)
    (_relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := tailStackReplayLimit ac count entryName alg regCount col loopEntry wordCtxt labels compiledCode loopLimit+1} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (_ha : ¬renamed.useAlloc) (_hs : ¬renamed.useStore) (_hk : ¬renamed.useStack)
    (_hf : Function.Bijective (findNameSpt f))
    (_hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (_hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (_labRel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (_hpc : LabSem.locToPc start 0 lab.code = some lab.pc)
    (_hmc : mc.target = riscvTarget) (_tie : LabToTarget.oracleTie mc machine lab)
    (_machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine),
    let out := (fullCompileSingle ac.twoRegArith regCount alg ac ((entryName,count,(LoopToWord.compHOL wordCtxt loopEntry labels).1),col)).2.2
    let stackLimit := tailStackReplayLimit ac count entryName alg regCount col loopEntry wordCtxt labels compiledCode loopLimit
    sptLookup entryName compiledCode = some (count,out) ∧
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F)
      (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F) (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit entry.code out (bs,n) (regCount,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := stackLimit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit entry.code out (bs,n) (regCount,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧ stackEntryClass stackResult = .CompleteResult outcome ∧
      ∃ wordPost wordResult perm selectedLocals targetPost,
        LoopToWord.CompileCorrect.resultCase wordCtxt (.loc 1 0) shiftedWord (resultToLoop result) loopPost wordResult wordPost ∧
        wordPost.ffi = loopPost.ffi ∧
        wordStateEqRel {wordPost with code := compiledCode,permute := perm,locals := selectedLocals,clock := tailWordReplayLimit loopEntry wordCtxt labels compiledCode loopLimit-(6*loopLimit-(6*loopLimit-(shiftedWord.clock-wordPost.clock)))} targetPost ∧
        compCorrectResult ac regCount frameSize frame
          {shiftedWord with code := compiledCode,locals := locals,clock := stackLimit}
          {targetPost with clock := stackLimit-(tailWordReplayLimit loopEntry wordCtxt labels compiledCode loopLimit-targetPost.clock)}
          stackPost wordResult stackResult lens ∧
        ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = panPost.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: panPost.ffi.ioEvents ∧
            targetPost.stackMax.getD (targetPost.stackLimit+1) > targetPost.stackLimit)) := by
  have codeRel := wholeCrep_supported_executable_codeRel arch crepPrograms entryName entryBody unique entryLookup programShapes
  rw [← ctxtEq, ← sourceCodeEq, ← loopCodeEq] at codeRel
  have loopWordCode := LoopToWordSteps.wholeCrepLoopWord_codeRel arch crepPrograms
  rw [← loopCodeEq, ← wordCodeEq] at loopWordCode
  obtain ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals⟩ := wordData
  have loopWordRel : loopToWordStateRelHOLExact target word :=
    ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals,loopWordCode⟩
  have shapes := WordAllocSteps.wholeCrep_word_shapes arch crepPrograms programShapes
  obtain ⟨value,condition,valueCompiled,conditionCompiled,post,result,postRel,resultRel,extra,loopPost,loopRel,backendTheorem⟩ :=
    panTailDeclEntry_compiled_riscvWithin ctxt live name source target word limit crepRel memRel globalsRel codeRel
      localsRel loopWordRel panLocal panInitializer panInit panCalleeInit panCondition panBody panTail callerContext sourceInitShape panInitializerShape panInitShape
      panConditionShape panBodyShape panTailShape pan panMiddle panPost panResult panLocals panReturnShape panInitRun
      panLookup panClock panRun panComplete initLocalised initialPanRel initialCodeRel initialExcpRel initialLocalsRel panBound
  refine ⟨shapes,value,condition,valueCompiled,conditionCompiled,post,result,postRel,resultRel,extra,loopPost,loopRel,?_⟩
  dsimp only
  intro ac count entryName alg regCount col wordCtxt labels compiledCode locals wordLocals retLookup dim retLabel vars gc
    wc programs programsEq entryMember algorithm registers colour wordCode compiledCodeEq localsRelWord domain
    stackEntry frameSize frame lens bs bsPost n nPost compiled start argumentCount stackRel native lengthBound bitmapBound
    bitmapPrefix labelCheck maxBound frameDef frameSizeDef space foundEntry inputCode anything cr c jump bounds pointer f gen
    maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine distinct sourceCode pre relation ha hs hk hf
    hcode hor labRel hpc hmc tie machineRel
  have actualShapes : TailProgramShapes programs := by rw [programsEq]; exact shapes
  have actualUnique : (programs.map Prod.fst).Nodup := by
    rw [programsEq]
    exact loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact arch crepPrograms)
  exact backendTheorem ac count entryName alg regCount col wordCtxt labels compiledCode locals wordLocals retLookup dim retLabel vars gc
    wc programs actualShapes entryMember actualUnique algorithm registers colour wordCode compiledCodeEq localsRelWord domain
    stackEntry frameSize frame lens bs bsPost n nPost compiled start argumentCount stackRel native lengthBound bitmapBound
    bitmapPrefix labelCheck maxBound frameDef frameSizeDef space foundEntry inputCode anything cr c jump bounds pointer f gen
    maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine distinct sourceCode pre relation ha hs hk hf
    hcode hor labRel hpc hmc tie machineRel

end SteppedFlapjack.PanToCrepSteps
