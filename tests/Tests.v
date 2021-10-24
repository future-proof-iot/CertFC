From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.


From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import DxIntegers DxList64 DxValues DxRegs DxOpcode DxMonad DxPointer DxFlag DxInstructions DxAST.

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
  DxPointer.Exports
  DxFlag.Exports
  DxAST.Exports
  eval_pc
  upd_pc
  eval_reg
  upd_reg
  eval_reg_mem
  upd_reg_mem
  load_mem
  store_mem
  __
  get_offset
  get_immediate
  list_get
  ins_to_opcode
  ins_to_dst_reg
  ins_to_src_reg
  normal_return
  succ_return
  ill_return
  ill_len
  ill_div
  ill_shift
  step
  bpf_interpreter_aux
  bpf_interpreter
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.