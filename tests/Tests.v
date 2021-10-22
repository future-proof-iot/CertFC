From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.


From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import DxIntegers DxList64 DxValues DxRegs DxZ DxOpcode DxMonad DxPointer DxFlag DxInstructions.

Definition test_array_op (a: ptr_int64) (index: int64_t)

(***************************************)


GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  DxIntegers.Exports
  DxList64.Exports
  DxValues.Exports
  DxRegs.Exports
  DxZ.Exports
  DxOpcode.Exports
  DxPointer.Exports
  DxFlag.Exports
  __(*
  get_opcode
  get_dst
  get_src
  get_offset
  get_immediate
  list_get
  ins_to_opcode
  ins_to_dst_reg
  ins_to_src_reg
  normal_return
  ill_return
  ill_len
  eval_regmapM
  upd_regmapM
  bpf_interpreter*)
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.