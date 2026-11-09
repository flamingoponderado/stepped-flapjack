import SteppedFlapjack.Concrete.ScalarEntry
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
set_option maxRecDepth 10000
theorem comparison_weight (arch : AsmArchitecture) :
  let ctxt := witnessLoopContext arch branchingHOL
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  loopVisitWeight (optimiseScalar (compileHOLExact c .ln branchCrepBody)) = 46 := by
  simp only [witnessLoopContext,ctxtFcExact,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq,
    branchCrepBody,compileHOLExact,compileExpHOLExact,compileExpsHOLExact,progIfHOLExact,
    genTemps,List.length_cons,List.length_nil,List.range_succ,List.range_zero,List.map_cons,List.map_nil,
    List.append_nil,List.nil_append,List.zipWith_cons_cons,List.zipWith_nil_left,Nat.add_zero]
  decide +kernel
theorem countdown_weight (arch : AsmArchitecture) (n : Nat) :
  let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  loopVisitWeight (optimiseScalar (compileHOLExact c .ln (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52 := by
  simp only [witnessLoopContext,ctxtFcExact,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq,
    naturalCountdownCrepBody,compileHOLExact,compileExpHOLExact,compileExpsHOLExact,
    genTemps,List.length_cons,List.length_nil,List.range_succ,List.range_zero,List.map_cons,List.map_nil,
    List.append_nil,List.nil_append,List.zipWith_cons_cons,List.zipWith_nil_left,Nat.add_zero]
  simp [optimiseScalar, scalarDepth, shrinkScalar, scalarFixedpoint, shrinkBranch,
    markAllHOL, loopVisitWeight, varsOfExpHOL, varsOfExpListHOL, loopNestedSeqHOL, FUPDATE_HOL,
    HolFiniteMapExact.updateEq, HolFiniteMapExact.empty, sptInsert, sptUnion, sptInter, sptSize, sptLookup, sptListInsert, sptDelete, sptOel, sptMkBN]

theorem conditional_weight (arch : AsmArchitecture) :
  let ctxt := witnessLoopContext arch (progToHOL branchingLoop)
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  loopVisitWeight (optimiseScalar (compileHOLExact c .ln branchingLoopCrepBody)) = 80 := by
  simp only [witnessLoopContext,ctxtFcExact,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq,
    branchingLoopCrepBody,compileHOLExact,compileExpHOLExact,compileExpsHOLExact,progIfHOLExact,
    genTemps,List.length_cons,List.length_nil,List.range_succ,List.range_zero,List.map_cons,List.map_nil,
    List.append_nil,List.nil_append,List.zipWith_cons_cons,List.zipWith_nil_left,Nat.add_zero]
  decide +kernel

/-- The actual liveness optimizer agrees with the executable calculation. -/
theorem comparison_optimized_weight (arch : AsmArchitecture) :
    let ctxt := witnessLoopContext arch branchingHOL
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    loopVisitWeight (optimiseHOL (compileHOLExact c .ln branchCrepBody)) = 46 := by
  let ctxt := witnessLoopContext arch branchingHOL
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  change loopVisitWeight (optimiseHOL (compileHOLExact c .ln branchCrepBody)) = 46
  rw [← optimiseScalar_eq (compile_scalar_program branching_scalar c .ln)]
  exact comparison_weight arch

theorem countdown_optimized_weight (arch : AsmArchitecture) (n : Nat) :
    let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    loopVisitWeight (optimiseHOL (compileHOLExact c .ln (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52 := by
  let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  change loopVisitWeight (optimiseHOL (compileHOLExact c .ln (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52
  rw [← optimiseScalar_eq (compile_scalar_program (naturalCountdown_scalar n) c .ln)]
  exact countdown_weight arch n

theorem conditional_optimized_weight (arch : AsmArchitecture) :
    let ctxt := witnessLoopContext arch (progToHOL branchingLoop)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    loopVisitWeight (optimiseHOL (compileHOLExact c .ln branchingLoopCrepBody)) = 80 := by
  let ctxt := witnessLoopContext arch (progToHOL branchingLoop)
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  change loopVisitWeight (optimiseHOL (compileHOLExact c .ln branchingLoopCrepBody)) = 80
  rw [← optimiseScalar_eq (compile_scalar_program branchingLoop_scalar c .ln)]
  exact conditional_weight arch


theorem envelope_46 : scalarOutputEnvelope 46 = 85838975299478796137350471140065246905153223130317616185985232102213238409 := by decide +kernel

theorem envelope_52 : scalarOutputEnvelope 52 = 90807393422973472024195615988211844816286992141046971418300877908670798816850466939403 := by decide +kernel

theorem envelope_80 : scalarOutputEnvelope 80 = 33055944283804003169638662153711282791046653244720418147730817235062148260722345963974318859772770346070640788027992384967906657677887271650360407 := by decide +kernel

end SteppedFlapjack.Concrete
