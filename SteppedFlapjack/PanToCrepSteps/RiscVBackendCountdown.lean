import Flapjack.Compiler.Backend.RiscVConfig.PancakeConfigOk

namespace SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig

/-- The actual GC-free RISC-V backend used by the Pancake compiler. -/
noncomputable def countdownRiscVBackend : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf riscvBackendConfig

end SteppedFlapjack.PanToCrepSteps
