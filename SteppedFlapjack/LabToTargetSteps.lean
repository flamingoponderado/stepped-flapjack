import SteppedFlapjack.LabToTargetSteps.Defs
import SteppedFlapjack.LabToTargetSteps.AsmStepEvaluate
import SteppedFlapjack.LabToTargetSteps.NopSteps
import SteppedFlapjack.LabToTargetSteps.BytesInMemoryFetch
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Common
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Step
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Asm
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Cbw
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Control
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.ShareMem
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.CallFfi
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Install
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Assembly
import SteppedFlapjack.LabToTargetSteps.RiscV

/-!
# Bounded `lab_to_target` simulation

Adapted copies of Flapjack's `lab_to_target` `compile_correct` proof in which
the target run is bounded (stepped-flapjack#2, phase B). With an encoder
correct within `steps` ticks per instruction (`encoderCorrectWithin`) and
`StepsFit unit steps`, `compileCorrectWithin` matches a source run with
clock `s1.clock` by a target run of at most
`labTickBound unit code2 s1.codeBuffer * s1.clock` ticks;
`compileCorrectWithin_riscv` instantiates it for RISC-V.
-/
