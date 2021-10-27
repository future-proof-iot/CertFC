From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.
 

From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import DxIntegers DxList64 DxValues DxRegs DxOpcode DxMonad DxFlag DxInstructions DxAST DxMemRegion.

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
  eval_flag
  upd_flag
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
  get_addl
  getMemRegion_block_ptr
  getMemRegion_start_addr
  getMemRegion_block_size
  getMemRegions_bpf_ctx
  getMemRegions_bpf_stk
  getMemRegions_content
  get_subl
  check_mem_aux
  check_mem
  step
  bpf_interpreter_aux
  bpf_interpreter
  test_reg_eval
  test_reg_upd
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.