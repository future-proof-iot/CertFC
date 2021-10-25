From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.
 

From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import DxIntegers DxList64 DxValues DxRegs DxOpcode DxMonad DxFlag DxInstructions DxAST DxMemRegion.

Definition getMemRegion (l3: MemRegionsType)(n3:nat): M memory_region := returnM (MemRegionsIndex l3 n3).

Definition getMemRegion_start_addr (l4: MemRegionsType)(n4:nat): M val64_t := returnM (start_addr (MemRegionsIndex l4 n4)).

Definition test_reg_eval (r0: reg) (regs0: regmap): M val64_t :=
  returnM (eval_regmap r0 regs0).

Definition test_reg_upd (r1: reg) (v: val64_t) (regs1: regmap): M regmap :=
  returnM (upd_regmap r1 v regs1).


(***************************************)


GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  DxIntegers.Exports
  DxList64.Exports
  DxValues.Exports
  DxRegs.Exports
  DxOpcode.Exports
  DxFlag.Exports
  DxAST.Exports
  DxMemRegion.Exports
  eval_pc
  upd_pc
  eval_reg
  upd_reg
  eval_reg_mem
  upd_reg_mem
  load_mem
  store_mem
  __
  list_get
  get_opcode
  get_dst
  get_src
  get_offset
  get_immediate
  succ_return
  normal_return
  ill_return
  ill_len
  ill_div
  ill_shift
  step
  bpf_interpreter_aux
  bpf_interpreter
  getMemRegion (*
  getMemRegion_start_addr *)
  test_reg_eval
  test_reg_upd
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.