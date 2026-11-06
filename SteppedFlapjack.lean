import SteppedFlapjack.LoopToWordSteps.FixedEntryRiscV
import SteppedFlapjack.WordToStackSteps.FixedEntryFrame
import SteppedFlapjack.WordToStackSteps.WholeEntryRiscV
import SteppedFlapjack.WordToStackSteps.WholeEntryFrame
import SteppedFlapjack.WordToStackSteps.InitialFrame
import SteppedFlapjack.WordToStackSteps.WholeInitialization
import SteppedFlapjack.WordToStackSteps.WholeProgram
import SteppedFlapjack.WordAllocSteps.WholeProgram
import SteppedFlapjack.PanToCrepSteps.ConditionBranchWhileWordAllocatedRiscV
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordAllocated
import SteppedFlapjack.WordAllocSteps.Prefix
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordCse
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordOptimized
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordCopy
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordDead
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordSsa
import SteppedFlapjack.WordSsaSteps.Selection
import SteppedFlapjack.PanToCrepSteps.ConditionBranchWhileWordSimpRiscV
import SteppedFlapjack.PanToCrepSteps.ConditionWordSimpRiscV
import SteppedFlapjack.LoopToWordSteps.WordSimpRiscV
import SteppedFlapjack.WordSimpSteps.RiscV
import SteppedFlapjack.WordSimpSteps.CompileLoop
import SteppedFlapjack.WordSimpSteps.PushBranch
import SteppedFlapjack.WordSimpSteps.Loop
import SteppedFlapjack.WordSimpSteps.Sequence
import SteppedFlapjack.PanToCrepSteps.ConditionBranchWhileRiscV
import SteppedFlapjack.PanToCrepSteps.ConditionRiscV
import SteppedFlapjack.PanToCrepSteps.BranchWhileRiscV
import SteppedFlapjack.PanToCrepSteps.WhileSequenceRiscV
import SteppedFlapjack.StackRemoveSteps.EmptyOracle
import SteppedFlapjack.PanToCrepSteps.WhileRiscV
import SteppedFlapjack.PanToCrepSteps.WhileSteps
import SteppedFlapjack.PanToCrepSteps.ControlSteps
import SteppedFlapjack.CrepSteps.WhileClock
import SteppedFlapjack.CrepSteps.BranchClock
import SteppedFlapjack.CrepToLoopSteps.WhileClock
import SteppedFlapjack.LoopSteps.IterationClock
import SteppedFlapjack.CrepToLoopSteps.BranchRiscV
import SteppedFlapjack.CrepToLoopSteps.WhileRiscV
import SteppedFlapjack.CrepToLoopSteps.WhileInduction
import SteppedFlapjack.CrepToLoopSteps.WhileIteration
import SteppedFlapjack.CrepToLoopSteps.BranchExtraClock
import SteppedFlapjack.CrepToLoopSteps.Branch
import SteppedFlapjack.LoopSteps.BranchedStatic
import SteppedFlapjack.LoopSteps.BranchedClock
import SteppedFlapjack.CrepToLoopSteps.ExprRiscV
import SteppedFlapjack.CrepToLoopSteps.ExprShape
import SteppedFlapjack.CrepToLoopSteps.ExprSequence
import SteppedFlapjack.LoopToWordSteps.SelectedRiscV
import SteppedFlapjack.LoopToWordSteps.SelectedComposition
import SteppedFlapjack.LoopToWordSteps.SelectedShape
import SteppedFlapjack.WordInstSteps.ProgramRiscV
import SteppedFlapjack.WordInstSteps.ProgramStack
import SteppedFlapjack.WordInstSteps.Compositional
import SteppedFlapjack.WordInstSteps.LoopGeneric
import SteppedFlapjack.WordInstSteps.LoopStack
import SteppedFlapjack.WordInstSteps.Loop
import SteppedFlapjack.WordInstSteps.Expression
import SteppedFlapjack.WordInstSteps.StackComposition
import SteppedFlapjack.WordInstSteps.Simple
import SteppedFlapjack.CrepToLoopSteps.RiscVComposition
import SteppedFlapjack.CrepToLoopSteps.BackendReady
import SteppedFlapjack.CrepToLoopSteps.WordComposition
import SteppedFlapjack.CrepToLoopSteps.Sequence
import SteppedFlapjack.LoopSteps.Clock
import SteppedFlapjack.CrepToLoopSteps.DirectLeaf
import SteppedFlapjack.CrepSteps.Defs
import SteppedFlapjack.LoopToWordSteps.LoopRiscV
import SteppedFlapjack.LoopToWordSteps.LoopProgram
import SteppedFlapjack.LoopToWordSteps.LoopBound
import SteppedFlapjack.LoopToWordSteps.LoopSetup
import SteppedFlapjack.LoopToWordSteps.LoopResult
import SteppedFlapjack.LoopToWordSteps.SixBound
import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.LoopToWordSteps.LoopCost
import SteppedFlapjack.LoopToWordSteps.ConditionalRiscV
import SteppedFlapjack.LoopToWordSteps.ConditionalStack
import SteppedFlapjack.LoopToWordSteps.Conditional
import SteppedFlapjack.LoopToWordSteps.RiscVComposition
import SteppedFlapjack.LoopToWordSteps.StackReady
import SteppedFlapjack.LoopToWordSteps.Sequence
import SteppedFlapjack.LoopSteps.DirectLeaf
import SteppedFlapjack.LoopSteps.Defs
import SteppedFlapjack.WordToStackSteps.EntryComposition
import SteppedFlapjack.WordToStackSteps.CallSequenceCost
import SteppedFlapjack.WordToStackSteps.CodeCostStable
import SteppedFlapjack.WordToStackSteps.CallSequence
import SteppedFlapjack.WordToStackSteps.ReturningHandlerComplete
import SteppedFlapjack.WordToStackSteps.ReturningHandlerZeroClock
import SteppedFlapjack.WordToStackSteps.ReturningNoneComplete
import SteppedFlapjack.WordToStackSteps.ReturningNoneSteps
import SteppedFlapjack.WordToStackSteps.ReturningZeroClock
import SteppedFlapjack.WordToStackSteps.ReturningNormalized
import SteppedFlapjack.WordToStackSteps.ReturningPrefixSteps
import SteppedFlapjack.WordToStackSteps.ReturningTargetSteps
import SteppedFlapjack.WordSteps.ReturningClock
import SteppedFlapjack.WordToStackSteps.TailCallSteps
import SteppedFlapjack.WordToStackSteps.TailCallZeroClock
import SteppedFlapjack.WordToStackSteps.LoopZeroClock
import SteppedFlapjack.WordToStackSteps.IfZeroClock
import SteppedFlapjack.WordToStackSteps.SequenceZeroClock
import SteppedFlapjack.WordToStackSteps.InstructionZeroClock
import SteppedFlapjack.WordToStackSteps.NormalizedClock
import SteppedFlapjack.WordSteps.ClockConsumption
import SteppedFlapjack.WordToStackSteps.Loops
import SteppedFlapjack.WordSteps.CallSteps
import SteppedFlapjack.StackToLabSteps.GeneratedHaltSteps
import SteppedFlapjack.StackToLabSteps.NamesComposition
import SteppedFlapjack.StackToLabSteps.FullInitLabSteps
import SteppedFlapjack.StackToLabSteps.FullInitRemoveLabSteps
import SteppedFlapjack.StackToLabSteps.FullInitAllocSteps
import SteppedFlapjack.StackToLabSteps.FullInitStackLabSteps
import SteppedFlapjack.StackToLabSteps.FullInitRiscVSteps
import SteppedFlapjack.StackToLabSteps.PipelineComposition
import SteppedFlapjack.StackToLabSteps.RiscVPipeline
import SteppedFlapjack.LabToTargetSteps.LabRiscVComposition
import SteppedFlapjack.StackRawCallSteps.LeafSteps
import SteppedFlapjack.StackRawCallSteps.IfSteps
import SteppedFlapjack.StackRawCallSteps.LoopSteps
import SteppedFlapjack.StackRawCallSteps.SeqStandardSteps
import SteppedFlapjack.StackRawCallSteps.SeqOptimizedCost
import SteppedFlapjack.StackRawCallSteps.SeqOptimizedSteps
import SteppedFlapjack.StackRawCallSteps.SeqSteps
import SteppedFlapjack.StackRawCallSteps.RawCallSteps
import SteppedFlapjack.StackRawCallSteps.JumpSteps
import SteppedFlapjack.StackRawCallSteps.CallTailSteps
import SteppedFlapjack.StackRawCallSteps.CallReturnSupport
import SteppedFlapjack.StackRawCallSteps.CallReturnSteps
import SteppedFlapjack.StackRawCallSteps.CompCorrect
import SteppedFlapjack.StackRawCallSteps.EntrySteps
import SteppedFlapjack.StackAllocSteps.AllocGenPartialSteps
import SteppedFlapjack.StackAllocSteps.AllocCorrectSteps
import SteppedFlapjack.StackAllocSteps.AllocCallSteps
import SteppedFlapjack.StackAllocSteps.AllocPassSteps
import SteppedFlapjack.StackAllocSteps.StoreConstsSteps
import SteppedFlapjack.StackAllocSteps.LeafSteps
import SteppedFlapjack.StackAllocSteps.ControlSteps
import SteppedFlapjack.StackAllocSteps.JumpSteps
import SteppedFlapjack.StackAllocSteps.CallSteps
import SteppedFlapjack.StackAllocSteps.CallReturnSteps
import SteppedFlapjack.StackAllocSteps.CompCorrect
import SteppedFlapjack.StackAllocSteps.EntrySteps
import SteppedFlapjack.StackAllocSteps.MakeInitEntrySteps
import SteppedFlapjack.StackAllocSteps.RawCallComposition
import SteppedFlapjack.StackAllocSteps.ThreePassComposition
import SteppedFlapjack.StackRemoveSteps.EntrySteps
import SteppedFlapjack.StackRemoveSteps.InitSteps
import SteppedFlapjack.StackRemoveSteps.InitEntrySteps
import SteppedFlapjack.StackRemoveSteps.InitHypSteps
import SteppedFlapjack.StackAllocSteps.UniformLeaf
import SteppedFlapjack.StackAllocSteps.AllocGenFullSteps
import SteppedFlapjack.StackAllocSteps.GenMoveLoopSteps
import SteppedFlapjack.StackAllocSteps.GenMoveDataSteps
import SteppedFlapjack.StackAllocSteps.GenMoveRootsSteps
import SteppedFlapjack.StackAllocSteps.GenMoveBitmapsSteps
import SteppedFlapjack.StackAllocSteps.GenMoveBitmapSteps
import SteppedFlapjack.StackAllocSteps.GenMoveBitmapCorrect
import SteppedFlapjack.StackAllocSteps.GenMoveListSteps
import SteppedFlapjack.StackAllocSteps.GenMoveListCorrect
import SteppedFlapjack.StackAllocSteps.GenMoveSteps
import SteppedFlapjack.StackAllocSteps.CollectorStructural
import SteppedFlapjack.StackAllocSteps.AllocNoneSteps
import SteppedFlapjack.StackAllocSteps.AllocSimpleSteps
import SteppedFlapjack.StackAllocSteps.AllocSimpleClock
import SteppedFlapjack.StackAllocSteps.AllocSimpleCorrect
import SteppedFlapjack.StackAllocSteps.GcMoveRootsSteps
import SteppedFlapjack.StackAllocSteps.GcMoveRootsClock
import SteppedFlapjack.StackAllocSteps.GcMoveRootsCorrect
import SteppedFlapjack.StackAllocSteps.GcMoveBitmapsSteps
import SteppedFlapjack.StackAllocSteps.GcMoveBitmapsClock
import SteppedFlapjack.StackAllocSteps.GcMoveBitmapsCorrect
import SteppedFlapjack.StackAllocSteps.GcMoveBitmapSteps
import SteppedFlapjack.StackAllocSteps.GcMoveBitmapClock
import SteppedFlapjack.StackAllocSteps.GcMoveBitmapCorrect
import SteppedFlapjack.StackAllocSteps.GcMoveLoopSteps
import SteppedFlapjack.StackAllocSteps.GcMoveLoopCorrect
import SteppedFlapjack.StackAllocSteps.GcMoveLoopClock
import SteppedFlapjack.StackAllocSteps.GcMoveListSteps
import SteppedFlapjack.StackAllocSteps.GcMoveSteps
import SteppedFlapjack.StackAllocSteps.GcMoveListCorrect
import SteppedFlapjack.StackAllocSteps.GcMoveClock
import SteppedFlapjack.StackAllocSteps.GcMoveCorrect
import SteppedFlapjack.StackAllocSteps.MemcpyCount
import SteppedFlapjack.StackAllocSteps.Memcpy
import SteppedFlapjack.StackAllocSteps.GcNone
import SteppedFlapjack.StackRemoveSteps.CompCorrect.FiniteAssembly
import SteppedFlapjack.PanValueExpCounted
import SteppedFlapjack.PanExpressionEvaluator
import SteppedFlapjack.PanSteppedSemantics
import SteppedFlapjack.PanValueFfiSemantics
import SteppedFlapjack.PanValueFfiFuel
import SteppedFlapjack.PanValueFfiEventMonotonicity
import SteppedFlapjack.PanValueFfiClockFuel
import SteppedFlapjack.PanValueFfiClockCorrectness
import SteppedFlapjack.PanValueFfiClockShift
import SteppedFlapjack.PanValueFfiClockProjection
import SteppedFlapjack.PanValueFfiClockStepsBridge
import SteppedFlapjack.PanCost
import SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge
import SteppedFlapjack.StepPreservation.Basic
import SteppedFlapjack.RiscVSteps
import SteppedFlapjack.LabToTargetSteps
import SteppedFlapjack.StackSteps.Defs
import SteppedFlapjack.StackSteps.AddClock
import SteppedFlapjack.StackNamesSteps
import SteppedFlapjack.StackToLabSteps
import SteppedFlapjack.StackRemoveSteps.Defs
import SteppedFlapjack.StackRemoveSteps.CopyEachSteps
import SteppedFlapjack.StackRemoveSteps.CopyLoopSteps
import SteppedFlapjack.StackRemoveSteps.StoreConstsSteps
import SteppedFlapjack.StackRemoveSteps.CompCorrect.StoreConsts
import SteppedFlapjack.StackRemoveSteps.LeafCostBounds
import SteppedFlapjack.StackRemoveSteps.LeafSteps
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Statement
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Seq
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Ite
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Loop
import SteppedFlapjack.StackRemoveSteps.CompCorrect.JumpLower
import SteppedFlapjack.StackRemoveSteps.CompCorrect.RawCall
import SteppedFlapjack.StackRemoveSteps.CallCostBounds
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Call
import SteppedFlapjack.StackRemoveSteps.CompCorrect.CallTail
import SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnNone
import SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnHandler
import SteppedFlapjack.StackRemoveSteps.CompCorrect.LeafStepsAll
import SteppedFlapjack.StackRemoveSteps.CodeBounds
import SteppedFlapjack.StackRemoveSteps.OraclePrefix
import SteppedFlapjack.StackRemoveSteps.InstallEffect
import SteppedFlapjack.StackRemoveSteps.OracleRunEffect
import SteppedFlapjack.StackRemoveSteps.OracleRunControl
import SteppedFlapjack.StackRemoveSteps.OracleRunLeaf
import SteppedFlapjack.StackRemoveSteps.OracleRunEvaluate
import SteppedFlapjack.StackRemoveSteps.CodeOrigin
import SteppedFlapjack.StackRemoveSteps.LeafCode
import SteppedFlapjack.StackRemoveSteps.CodeOriginEvaluate
import SteppedFlapjack.StackRemoveSteps.RunBudget
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Leaf

/-!
# stepped-flapjack

The step-counted structured Pancake source semantics, split out of Flapjack in
phase 4 of flapjack#1251:

- `SteppedFlapjack.PanValueExpCounted`, `SteppedFlapjack.PanExpressionEvaluator`:
  expression evaluators that count steps;
- `SteppedFlapjack.PanSteppedSemantics`, `SteppedFlapjack.PanValueFfiSemantics`:
  the stepped statement evaluators, including `evalPanValueFfiProgSteps`;
- `SteppedFlapjack.PanValueFfiFuel`, `SteppedFlapjack.PanValueFfiEventMonotonicity`:
  fuel and I/O-event monotonicity of the stepped evaluator;
- `SteppedFlapjack.PanValueFfiClockFuel`, `SteppedFlapjack.PanValueFfiClockCorrectness`,
  `SteppedFlapjack.PanValueFfiClockShift`: fuel and clock properties of the
  Flapjack-specific clocked evaluator;
- `SteppedFlapjack.PanValueFfiClockProjection`,
  `SteppedFlapjack.PanValueFfiClockStepsBridge`: the bridge from Flapjack's
  clocked evaluator to stepped results, which cannot cover timed-out runs;
- `SteppedFlapjack.PanCost`: source-level step costs;
- `SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge`: the
  counted expression evaluator against `PanSem.evalExecuted`;
- `SteppedFlapjack.StepPreservation.Basic`: linear step bounds, their
  composition across passes, and machine step counts (stepped-flapjack#2);
- `SteppedFlapjack.RiscVSteps`: adapted copies of Flapjack's RISC-V encoder
  correctness cases with each step count bounded, assembled as
  `riscv_encoder_correct_within` (stepped-flapjack#2, phase A);
- `SteppedFlapjack.LabToTargetSteps`: adapted copies of Flapjack's
  `lab_to_target` `compile_correct` proof with the target run bounded by
  `labTickBound` ticks per source clock tick, assembled as
  `compileCorrectWithin` and specialised to RISC-V as
  `compileCorrectWithin_riscv` (stepped-flapjack#2, phase B);
- `SteppedFlapjack.StackSteps.Defs`: `steps`, a fine-grained step count of a
  StackSem run, counting every `evaluate` invocation (stepped-flapjack#2,
  phase C);
- `SteppedFlapjack.StackSteps.AddClock`: `steps_addClock`, clock monotonicity
  of the step count — a run that does not time out takes the same number of
  steps at any larger clock, which is what lets a run-clock bound be reused
  when the compiler correctness induction raises a `Seq`'s second clock
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackToLabSteps`: adapted copies of Flapjack's `stack_to_lab`
  `flatten_correct` proof with the LabSem run bounded by `flattenStepFactor`
  ticks per StackSem step, assembled as `flattenCorrectWithin` and lifted to
  the start call as `flattenSemanticsWithin` (stepped-flapjack#2, phase C1);
- `SteppedFlapjack.StackAllocSteps.UniformLeaf`: a uniform leaf factor for
  word widths of at least eight bits, independent of runtime stack length.
- `SteppedFlapjack.StackAllocSteps.MakeInitEntrySteps`: bounded entry
  simulation for the actual allocation make-init state.
- `SteppedFlapjack.WordToStackSteps.Basic`, `Instructions`: exact basic-case
  and structural machine-instruction runtime bounds for Word-to-Stack compilation.
- `SteppedFlapjack.WordToStackSteps.StraightLine`: a proved bound for nested
  sequences and branches in a loop-free, call-free WordSem fragment.
- `SteppedFlapjack.WordToStackSteps.ReturningNoneComplete`: source-step-based
  no-handler bound for all non-error, non-timeout outcomes.
- `SteppedFlapjack.WordToStackSteps.ReturningNoneSteps`: complete no-handler
  zero-clock simulation and a source-step-based matching-return bound.
- `SteppedFlapjack.LoopToWordSteps.SixBound`: sixfold sequence and conditional simulation.
- `SteppedFlapjack.LoopToWordSteps.LoopResult`: loop-result classification.
- `SteppedFlapjack.LoopToWordSteps.LoopSetup`: derived loop cut and timeout setup.
- `SteppedFlapjack.LoopToWordSteps.LoopBound`: quantitative loop induction.
- `SteppedFlapjack.LoopToWordSteps.LoopProgram`: nested-loop fragment and Word compilation shape.
- `SteppedFlapjack.LoopToWordSteps.SelectedRiscV`: Loop runs through instruction selection and RISC-V.
- `SteppedFlapjack.LoopToWordSteps.SelectedComposition`: Loop-to-selected-Word semantic and step composition.
- `SteppedFlapjack.LoopToWordSteps.SelectedShape`: Loop compiler output accepted by instruction-selection bounds.
- `SteppedFlapjack.LoopToWordSteps.LoopRiscV`: nested-loop executions composed through RISC-V.
- `SteppedFlapjack.LoopToWordSteps.Outcome`: source-to-machine outcome and trace correspondence.
- `SteppedFlapjack.LoopToWordSteps.LoopCost`: cost of the compiled loop wrapper and continuing iterations.
- `SteppedFlapjack.LoopToWordSteps.Conditional`: Loop-to-Word step preservation with conditional branches.
- `SteppedFlapjack.LoopToWordSteps.ConditionalStack`: conditional source programs in the proved Word-to-Stack fragment.
- `SteppedFlapjack.LoopToWordSteps.ConditionalRiscV`: conditional Loop programs composed through the RISC-V backend.
- `SteppedFlapjack.LoopToWordSteps.Sequence`: Loop-to-Word step preservation for direct statements, sequences, and marks.
- `SteppedFlapjack.LoopToWordSteps.StackReady`: common Loop-to-Stack fragment and composed bounded simulation.
- `SteppedFlapjack.LoopToWordSteps.RiscVComposition`: bounded Loop execution composed through the RISC-V backend.
- `SteppedFlapjack.WordInstSteps.ProgramRiscV`: compositional selected Word programs through RISC-V.
- `SteppedFlapjack.WordInstSteps.ProgramStack`: compositional selected programs through Stack.
- `SteppedFlapjack.WordInstSteps.Compositional`: bottom-up bounds for sequences, branches and nested loops.
- `SteppedFlapjack.WordInstSteps.LoopGeneric`: quantitative loop induction from an established body bound.
- `SteppedFlapjack.WordInstSteps.LoopStack`: selected Word loops composed through Stack.
- `SteppedFlapjack.WordInstSteps.Loop`: iteration-sensitive instruction-selection bounds.
- `SteppedFlapjack.WordInstSteps.StackComposition`: bounded selected Word runs through Stack.
- `SteppedFlapjack.WordInstSteps.Expression`: general selected-expression shape, conventions and cost.
- `SteppedFlapjack.WordInstSteps.Simple`: quantitative instruction selection for Word expression statements.
- `SteppedFlapjack.CrepSteps.WhileClock`: source while-loop clock consumption bounded by visits.
- `SteppedFlapjack.CrepSteps.BranchClock`: source branch-program clock consumption bounded by visits.
- `SteppedFlapjack.CrepToLoopSteps.WhileClock`: compiled while loops bounded by clock consumption.
- `SteppedFlapjack.CrepToLoopSteps.BranchRiscV`: Crep conditional programs through RISC-V.
- `SteppedFlapjack.StackRemoveSteps.EmptyOracle`: constant Stack-removal cost for an empty-install oracle.
- `SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordOptimized`: Crep initialization, loop and continuation through all pre-allocation Word optimizations.
- `SteppedFlapjack.WordDeadSteps.Second`: semantic and visit bound through the second dead-code pass.
- `SteppedFlapjack.WordUnreachSteps.Correct`: semantic and visit bound through unreachable removal.
- `SteppedFlapjack.WordTwoRegSteps.Correct`: semantic and visit bound through three-to-two rewriting.
- `SteppedFlapjack.WordCopySteps.Correct`: semantic and visit bound through copy propagation.
- `SteppedFlapjack.WordCseSteps.Correct`: semantic and visit bound through CSE.
- `SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordDead`: Crep initialization, loop and continuation through first dead-code elimination.
- `SteppedFlapjack.LoopToWordSteps.WordDeadSequence`: Loop sequences through SSA and first dead-code elimination.
- `SteppedFlapjack.WordDeadSteps.Correct`: dead-code semantics and source-relative visit bounds.
- `SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordSsa`: Crep initialization, loop and continuation through full SSA.
- `SteppedFlapjack.LoopToWordSteps.WordSsaSequence`: Loop sequences through the full SSA prefix.
- `SteppedFlapjack.WordSsaSteps.Composition`: WordSimp, instruction selection and SSA semantics and visit bound.
- `SteppedFlapjack.WordSsaSteps.Permute`: permutation independence for supported loops and branches.
- `SteppedFlapjack.WordSsaSteps.Selection`: actual WordSimp, selection and SSA prefix has a syntax-and-clock visit bound.
- `SteppedFlapjack.WordSsaSteps.Program`: full SSA preserves branch-bodied loop sequences.
- `SteppedFlapjack.WordSsaSteps.Branch`: SSA branch bodies have a static visit bound.
- `SteppedFlapjack.PanToCrepSteps.ConditionBranchWhileWordSimpRiscV`: Pancake initialization, comparison loop and continuation through WordSimp to RISC-V.
- `SteppedFlapjack.LoopToWordSteps.WordSimpSequenceRiscV`: source-relative WordSimp sequence bound through RISC-V.
- `SteppedFlapjack.WordSimpSteps.LoopSequenceBound`: normalized source-step bound for WordSimp loop sequences.
- `SteppedFlapjack.PanToCrepSteps.ConditionWordSimpRiscV`: comparison-controlled Pancake loops through WordSimp to RISC-V.
- `SteppedFlapjack.CrepToLoopSteps.ConditionWordSimpRiscV`: Crep comparison-controlled loops through WordSimp to RISC-V.
- `SteppedFlapjack.CrepToLoopSteps.WordSimpShape`: derives generated Loop branch shapes.
- `SteppedFlapjack.LoopToWordSteps.WordSimpRiscV`: Loop-to-RISC-V bound including actual WordSimp for supported loop bodies.
- `SteppedFlapjack.LoopToWordSteps.WordSimpLoop`: Loop-to-WordSimp visits and derived output shape.
- `SteppedFlapjack.WordSimpSteps.TickLoop`: WordSimp bound on the tick-wrapped compiled loop.
- `SteppedFlapjack.WordSimpSteps.RiscV`: WordSimp and instruction selection through the bounded RISC-V backend.
- `SteppedFlapjack.WordSimpSteps.Stack`: WordSimp and selection through Word-to-Stack.
- `SteppedFlapjack.WordSimpSteps.Selection`: WordSimp composed with instruction selection.
- `SteppedFlapjack.WordSimpSteps.CompileLoop`: complete WordSimp semantics and visit bounds for loops with branch bodies.
- `SteppedFlapjack.WordSimpSteps.CompileBranch`: complete WordSimp semantics and visit bounds for loop-free branches.
- `SteppedFlapjack.WordSimpSteps.HoistBranch`: duplicate-conditional hoisting preserves branch shape.
- `SteppedFlapjack.WordSimpSteps.PushBranch`: conditional push-out preserves bounded branch shape.
- `SteppedFlapjack.WordSimpSteps.ConstBranch`: sequence normalization and constant propagation on branches.
- `SteppedFlapjack.WordSimpSteps.Branch`: bounds for branch and loop sequence normalization.
- `SteppedFlapjack.WordSimpSteps.Loop`: complete WordSimp pass on loops with straight-line bodies.
- `SteppedFlapjack.WordSimpSteps.Straight`: complete WordSimp pass on straight-line code.
- `SteppedFlapjack.WordSimpSteps.Sequence`: sequence reassociation visit bounds and straight-line normalization.
- `SteppedFlapjack.PanToCrepSteps.ConditionBranchWhileRiscV`: initialization, comparison-controlled loop, and continuation through RISC-V.
- `SteppedFlapjack.PanToCrepSteps.ConditionRiscV`: comparison-controlled loop through RISC-V.
- `SteppedFlapjack.CrepToLoopSteps.ConditionInduction`: bounded compiler clock and visits for comparison-controlled loops.
- `SteppedFlapjack.PanToCrepSteps.BranchWhileRiscV`: initialization, loop and continuation through RISC-V.
- `SteppedFlapjack.PanToCrepSteps.BranchWhile`: initialization and loop through the Pancake frontend.
- `SteppedFlapjack.CrepToLoopSteps.BranchWhileRiscV`: Crep initialization and loop through RISC-V.
- `SteppedFlapjack.CrepToLoopSteps.BranchPrefix`: compositional branch-prefix visit bounds.
- `SteppedFlapjack.PanToCrepSteps.WhileSequenceRiscV`: Pancake loops with continuations through RISC-V.
- `SteppedFlapjack.PanToCrepSteps.WhileSequence`: source-to-Crep loop and continuation bound.
- `SteppedFlapjack.CrepToLoopSteps.WhileSequenceRiscV`: Crep loops with continuations through RISC-V.
- `SteppedFlapjack.CrepToLoopSteps.WhileSequence`: Crep-to-Loop sequence bound.
- `SteppedFlapjack.LoopSteps.IterationShift`: loop visit stability under clock extension.
- `SteppedFlapjack.PanToCrepSteps.WhileRiscV`: Pancake loop visits through instruction selection to RISC-V.
- `SteppedFlapjack.PanToCrepSteps.WhileSteps`: semantic and quantitative Pancake-to-Crep loop correctness.
- `SteppedFlapjack.PanToCrepSteps.ControlSteps`: exact-state source control visits and compiled branch bounds.
- `SteppedFlapjack.PanToCrepSteps.Shape`: source fragments lowered to supported Crep.
- `SteppedFlapjack.CrepSteps.BranchStatic`: syntax-size bounds for loop-free Crep visits.
- `SteppedFlapjack.CrepToLoopSteps.WhileRiscV`: Crep while loops through instruction selection and RISC-V.
- `SteppedFlapjack.CrepToLoopSteps.WhileInduction`: source-step bounds on compiled Crep while loops.
- `SteppedFlapjack.CrepToLoopSteps.WhileIteration`: compiled loop executions for false and continuing direct guards.
- `SteppedFlapjack.CrepToLoopSteps.DirectExpressionEval`: direct condition evaluation with no extra clock.
- `SteppedFlapjack.CrepToLoopSteps.BranchExtraClock`: syntax bound on compiler extra clock for Crep branch programs.
- `SteppedFlapjack.CrepToLoopSteps.Branch`: Crep conditional compilation and source-step bounds.
- `SteppedFlapjack.LoopSteps.IterationClock`: loop visits bounded by consumed clock and body size.
- `SteppedFlapjack.LoopSteps.ClockConsumption`: loop-free branch clock consumption bounded by visits.
- `SteppedFlapjack.LoopSteps.BranchedStatic`: loop-free branch visit bounds.
- `SteppedFlapjack.LoopSteps.BranchedClock`: branch count stability under clock extension.
- `SteppedFlapjack.CrepToLoopSteps.ExprRiscV`: Crep expression programs through instruction selection and RISC-V.
- `SteppedFlapjack.CrepToLoopSteps.ExprShape`: compiled Crep expression programs fit selected Loop bounds.
- `SteppedFlapjack.CrepToLoopSteps.ExprSequence`: Crep assignment and sequence bounds.
- `SteppedFlapjack.CrepToLoopSteps.RiscVComposition`: completed Crep runs through the bounded RISC-V backend.
- `SteppedFlapjack.CrepToLoopSteps.BackendReady`: compiled fragment and completed outcome bridge to the backend.
- `SteppedFlapjack.CrepToLoopSteps.WordComposition`: Crep-to-Word bounded execution for direct sequences.
- `SteppedFlapjack.CrepToLoopSteps.Sequence`: quantitative Crep-to-Loop correctness for direct sequences.
- `SteppedFlapjack.CrepToLoopSteps.DirectLeaf`: semantic and exact step preservation for direct Crep leaves.
- `SteppedFlapjack.CrepSteps.Defs`: exact Crep statement counts and basic control-flow equations.
- `SteppedFlapjack.LoopSteps.Clock`: clock-extension stability for direct sequential Loop runs.
- `SteppedFlapjack.LoopSteps.Defs`: exact-evaluator LoopSem statement counts and control-flow equations.
- `SteppedFlapjack.LoopSteps.DirectLeaf`: direct Loop-to-Word semantic correctness with exact step counts.
- `SteppedFlapjack.WordToStackSteps.EntryComposition`: bounded Word call sequences composed through the RISC-V backend.
- `SteppedFlapjack.WordToStackSteps.CallSequenceCost`: computable target-step bounds for sequences containing calls.
- `SteppedFlapjack.WordToStackSteps.CodeCostStable`: stability and clock monotonicity of computable call costs.
- `SteppedFlapjack.WordToStackSteps.CallSequence`: source-clock accounting and zero-clock simulation for sequences containing calls.
- `SteppedFlapjack.WordToStackSteps.ReturningHandlerComplete`: source-step bounds and compiled execution for returning handler calls over loop blocks.
- `SteppedFlapjack.WordToStackSteps.ReturningHandlerZeroClock`: zero-clock handler callee and continuation proofs for loop blocks.
- `SteppedFlapjack.WordToStackSteps.ReturningZeroClock`: zero-clock callee and
  matching normal-return continuation composition from the actual call history.
- `SteppedFlapjack.WordToStackSteps.ReturningNormalized`: source-step clock
  normalization and target bounds for matching return and exception paths.
- `SteppedFlapjack.WordToStackSteps.ReturningPrefixSteps`: structural bounds
  for complete compiled returning-call setup and continuations.
- `SteppedFlapjack.WordToStackSteps.ReturningTargetSteps`: target returning-call
  bounds and call-free setup/continuation shape proofs.
- `SteppedFlapjack.WordToStackSteps.TailCallSteps`: source-step-based target
  bounds for tail calls into loop-block source code.
- `SteppedFlapjack.WordToStackSteps.TailCallZeroClock`: zero-clock tail-call
  simulation with the callee case discharged for loop-block code.
- `SteppedFlapjack.WordToStackSteps.LoopZeroClock`: zero-clock loop simulation
  and a source-step-based target bound for nested loop blocks.
- `SteppedFlapjack.WordToStackSteps.IfZeroClock`: zero-clock branch simulation
  and a target-step bound for nested branching instruction blocks.
- `SteppedFlapjack.WordToStackSteps.SequenceZeroClock`: compositional zero-clock
  simulation and target-step bound for instruction blocks.
- `SteppedFlapjack.WordToStackSteps.InstructionZeroClock`: outcome-preserving
  machine-instruction simulation with no additional target clock.
- `SteppedFlapjack.WordToStackSteps.NormalizedClock`: source replay at a
  supplied step bound and a corresponding target structural bound.
- `SteppedFlapjack.WordToStackSteps.Loops`: structural target-step bounds for
  compiled call-free loops, in terms of the actual initial clock.
- `SteppedFlapjack.WordSteps.Defs`: a WordSem evaluator-invocation counter
  with checked leaf, sequence, conditional, loop, and tail-call equations.
- `SteppedFlapjack.WordSteps.ReturningClock`: clock-consumption bounds for
  matching normal and exception returning-call continuations.
- `SteppedFlapjack.WordSteps.ClockConsumption`: actual clock consumed by
  call-free loop-fragment runs is bounded by their evaluator step count.
- `SteppedFlapjack.WordSteps.CallSteps`: returning-call equations covering all
  callee results after successful call setup.
- `SteppedFlapjack.StackToLabSteps.FullInitAllocSteps`, `FullInitStackLabSteps`,
  `FullInitRiscVSteps`: actual initialized stack execution through RISC-V.
- `SteppedFlapjack.StackToLabSteps.FullInitRemoveLabSteps`: bounded actual
  stack-removal initialization composed through LabSem.
- `SteppedFlapjack.StackRemoveSteps.InitEntrySteps`, `InitHypSteps`: initialized
  entry bounds and their derivation from compiler initialization bundles.
- `SteppedFlapjack.StackRemoveSteps.InitSteps`: a clock-independent bound
  for generated initialization and its entry overhead.
- `SteppedFlapjack.StackToLabSteps.FullInitLabSteps`: the bounded Lab stage
  with state relations derived from full compiler initialization.
- `SteppedFlapjack.StackToLabSteps.RiscVPipeline`: the bounded stack backend
  composed through LabSem to a RISC-V target run.
- `SteppedFlapjack.StackToLabSteps.NamesComposition`, `PipelineComposition`:
  bounded composition of the completed stack passes through LabSem.
- `SteppedFlapjack.StackToLabSteps.GeneratedHaltSteps`: a four-step bound
  for the generated halt procedure and bounded flattening without a cost assumption.
- `SteppedFlapjack.StackAllocSteps.ThreePassComposition`: an entry-step
  bound composing raw-call optimization, allocation, and stack removal.
- `SteppedFlapjack.StackRawCallSteps.EntrySteps` and
  `StackAllocSteps.RawCallComposition`: entry simulations and their composition.
- `SteppedFlapjack.StackRawCallSteps.CallReturnSupport`, `CallReturnSteps`,
  `CompCorrect`: returning-call bounds and the complete raw-call pass theorem.
- `SteppedFlapjack.StackRawCallSteps.CallTailSteps`: a nonincreasing bound
  for ordinary tail calls.
- `SteppedFlapjack.StackRawCallSteps.RawCallSteps`, `JumpSteps`: nonincreasing
  bounds for code-lookup control transfers.
- `SteppedFlapjack.StackRawCallSteps.SeqOptimizedSteps`, `SeqSteps`: the
  optimized and complete sequence step-preservation cases.
- `SteppedFlapjack.StackRawCallSteps.SeqOptimizedCost`: bounds for successful,
  timed-out, and allocation-failing frame transfers.
- `SteppedFlapjack.StackRawCallSteps.SeqStandardSteps`: the ordinary sequence
  case for raw-call step preservation.
- `SteppedFlapjack.StackRawCallSteps.LoopSteps`: a nonincreasing step bound
  for raw-call loop iterations, exits, and timeouts.
- `SteppedFlapjack.StackRawCallSteps.IfSteps`: a nonincreasing step bound for
  raw-call conditional branches.
- `SteppedFlapjack.StackRawCallSteps.LeafSteps`: exact one-step bounds for
  nonrecursive raw-call optimization cases.
- `SteppedFlapjack.StackAllocSteps.EntrySteps`: the bounded entry-call
  simulation for stack allocation.
- `SteppedFlapjack.StackAllocSteps.CompCorrect`: uniform step-preservation
  for stack allocation on words of at least eight bits.
- `SteppedFlapjack.StackAllocSteps.CallReturnSteps`: returning calls with
  normal and exception continuations.
- `SteppedFlapjack.StackAllocSteps.CallSteps`: the bounded tail-call case.
- `SteppedFlapjack.StackAllocSteps.JumpSteps`: step bounds for indirect
  jumps and raw calls through compiled code.
- `SteppedFlapjack.StackAllocSteps.ControlSteps`: step-counted sequence,
  conditional, and loop cases for the stack-allocation simulation.
- `SteppedFlapjack.StackAllocSteps.LeafSteps`: a combined bound for every
  nonrecursive source statement in stack allocation.
- `SteppedFlapjack.StackAllocSteps.StoreConstsSteps`: the store-constants pass
  case and generated stub use at most five target steps.
- `SteppedFlapjack.StackAllocSteps.AllocCorrectSteps`, `AllocCallSteps`,
  `AllocPassSteps`: collector-independent allocation bounds, including the
  generated call and the stack-allocation pass case.
- `SteppedFlapjack.StackAllocSteps.AllocGenPartialCorrect`, `AllocGenPartialSteps`:
  partial generational allocation correctness with a target-step bound;
- `SteppedFlapjack.StackAllocSteps.AllocGenFullCorrect`, `AllocGenFullSteps`:
  full generational allocation correctness with a target-step bound;
- `SteppedFlapjack.StackAllocSteps.GenMoveLoopCorrect`, `GenMoveLoopSteps`:
  clock and fuel-based bounds for the full generational collector loop;
- `SteppedFlapjack.StackAllocSteps.GenMoveDataCorrect`, `GenMoveDataSteps`:
  clock and fuel-based bounds for generational data and references;
- `SteppedFlapjack.StackAllocSteps.GenMoveRootsCorrect`, `GenMoveRootsSteps`:
  clock and stack-length bounds for generational root traversal;
- `SteppedFlapjack.StackAllocSteps.GenMoveBitmapsCorrect`, `GenMoveBitmapsSteps`:
  clock and count-based bounds for generational bitmap lists;
- `SteppedFlapjack.StackAllocSteps.GenMoveBitmapCorrect`, `GenMoveBitmapSteps`:
  clock and value-based step bounds for generational bitmap traversal;
- `SteppedFlapjack.StackAllocSteps.GenMoveListCorrect`, `GenMoveListSteps`:
  clock and length-based step bounds for generational object lists;
- `SteppedFlapjack.StackAllocSteps.GenMoveCorrect`, `GenMoveSteps`:
  clock and step bounds for full and partial generational object movement;
- `SteppedFlapjack.StackAllocSteps.BoundedNormal`: clock-independent bounds
  from a bounded normal run;
- `SteppedFlapjack.StackAllocSteps.CollectorStructural`: a structural step
  bound for every configured collector, indexed by its available clock;
- `SteppedFlapjack.StackAllocSteps.AllocNoneSteps`: no-collector allocation
  correctness with a 15-step bound;
- `SteppedFlapjack.StackAllocSteps.AllocSimpleCorrect`, `AllocSimpleClock`,
  `AllocSimpleSteps`: simple allocation correctness with a target-step bound;
- `SteppedFlapjack.StackAllocSteps.GcMoveRootsClock`, `GcMoveRootsCorrect`,
  `GcMoveRootsSteps`: clock and stack-length bounds for root traversal;
- `SteppedFlapjack.StackAllocSteps.GcMoveBitmapsClock`, `GcMoveBitmapsCorrect`,
  `GcMoveBitmapsSteps`: clock and count-based bounds for bitmap-list traversal;
- `SteppedFlapjack.StackAllocSteps.GcMoveBitmapClock`, `GcMoveBitmapCorrect`,
  `GcMoveBitmapSteps`: clock and value-based step bounds for bitmap traversal;
- `SteppedFlapjack.StackAllocSteps.GcMoveLoopCorrect`, `GcMoveLoopClock`,
  `GcMoveLoopSteps`: clock and fuel-based step bounds for heap traversal;
- `SteppedFlapjack.StackAllocSteps.GcMoveClock`, `GcMoveCorrect`, `GcMoveSteps`,
  `GcMoveListCorrect`, `GcMoveListSteps`: bounds and correctness for object movement and lists;
- `SteppedFlapjack.StackAllocSteps.Memcpy`, `SteppedFlapjack.StackAllocSteps.MemcpyCount`:
  memory-copy body, loop and word-count step bounds;
- `SteppedFlapjack.StackAllocSteps.GcNone`: a 15-step bound for allocation
  code when no garbage collector is selected;
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.FiniteAssembly`: a stack-removal
  run bound with finite code, oracle and bitmap budgets computed from the initial
  state and source-step bound;
- `SteppedFlapjack.StackRemoveSteps.Defs`: program-dependent expansion costs for
  the `stack_remove` pass, including `leafCost` and the step-count bounds for
  the `upshift`, `downshift` and `stackFree` expansions
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CopyEachSteps`: the per-bitmap-word copy
  loop's fine-grained step bound `15 * (pattern.toNat + 1) + 3`, carried by an
  adapted `copyEachThmWithin` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.LeafCostBounds`: `leafCost` is at least one
  and dominates every subprogram's factor, which is what lets the `stack_remove`
  correctness induction thread one program-dependent factor down the tree
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.LeafSteps`: for every leaf with a nontrivial
  expansion, the compiled form takes at most `leafCost B bounds` steps from any
  state — the leaf half of the top-level step bound (stepped-flapjack#2, phase
  C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CopyLoopSteps`: the outer bitmap-list copy
  loop's bound `copyLoopSteps width (bitmaps.length - index)`, carried by an
  adapted `copyLoopThmWithin` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Statement`: the step-counted
  `stack_remove` statement shape and the `bitmapBound B` hypothesis that
  discharges the `storeConsts` bitmap-length bound at the top theorem
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Seq`: the `Seq` induction case of
  the step-counted correctness theorem, adding `steps <= leafCost * steps` to
  Flapjack's `compCorrectSeq` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Ite`: the `ite` case, adding the
  step bound to `compCorrectIf` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Loop`: the `loop` case, adding
  the step bound to `compCorrectLoop` along both the exit and the reentry
  branches (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.JumpLower`: the `jumpLower`
  case. It runs a program from the code, so it takes the code-bound hypothesis
  `codeBound` and concludes against the program-dependent factor `K`
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.RawCall`: the `rawCall` case,
  likewise concluding against `K` from the code bound (stepped-flapjack#2,
  phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CallCostBounds`: `leafCost` dominates the
  `call` constructor's return and handler bodies (stepped-flapjack#2, phase C3,
  in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.CallTail`: the `ret = none`
  `call` case, taking the code bound for the callee (stepped-flapjack#2,
  phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnNone`: the returning
  `call` with no handler, threading both the callee's code bound and the return
  continuation's structural bound (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnHandler`: the returning
  `call` with an exception handler, adding the successful-exception branch
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Call`: the `call` assembly,
  dispatching on the `ret`/`handler` shapes (stepped-flapjack#2, phase C3,
  in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.LeafStepsAll`: one step bound
  covering all 28 non-recursive constructors, so the top-level induction needs a
  single leaf case (stepped-flapjack#2, phase C3, in progress).
- `SteppedFlapjack.StackNamesSteps`: adapted copies of Flapjack's `stack_names`
  `comp_correct` proof with the step count preserved exactly, assembled as
  `steps_progCompHOL` and `compCorrectWithin`, and lifted to the entry run from
  `make_init` as `stackNamesSemanticsWithin` (stepped-flapjack#2, phase C2).

Module names moved from `Flapjack.*` to `SteppedFlapjack.*`; declarations keep
their names in the `Flapjack` namespace. The tests are in the separate
`SteppedFlapjackTests` library, rooted at `SteppedFlapjack.Tests`.
-/
