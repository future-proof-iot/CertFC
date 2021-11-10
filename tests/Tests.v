From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.
 

From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import DxIntegers DxList64 DxValues DxRegs DxState DxOpcode DxMonad DxFlag DxInstructions DxAST DxMemRegion.

(***************************************)


GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  DxIntegers.Exports
  DxList64.Exports
  DxValues.Exports
  DxRegs.Exports
  DxState.Exports
  DxOpcode.Exports
  DxFlag.Exports
  DxAST.Exports
  DxMemRegion.Exports
  eval_pc
  upd_pc
  upd_pc_incr
  eval_reg
  upd_reg
  eval_flag
  upd_flag (*
  eval_mem_regions
  upd_mem_regions*)
  load_mem
  store_mem_imm
  store_mem_reg
  __
  list_get
  get_opcode
  get_dst
  get_src
  get_offset
  get_immediate
  get_addl
  get_subl
  getMemRegion_block_ptr
  getMemRegion_start_addr
  getMemRegion_block_size
  is_well_chunk_bool
  check_mem_aux
  check_mem
  step
  bpf_interpreter_aux
  bpf_interpreter
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.