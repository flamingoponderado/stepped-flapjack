import Flapjack.Compiler.Backend.RiscVConfig.Executable
import SteppedFlapjack.PanToCrepSteps.CountdownExecutableCompiler
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.PanToCrepSteps
/-- info: some (1, some [], 0) -/
#guard_msgs in
#eval (compileProgMaxAsmExecutable (Flapjack.Compiler.pancakeBackendConf riscvBackendConfigExecutable) riscvConfig
  (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
    (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
    (.return (.const (0 : BitVec 64)))))))).1.map (fun (_, bm, c) => (bm.length,c.labConf.ffiNames,c.labConf.shmemExtra.length))
