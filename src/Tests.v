From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.
 

From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
From bpf.src Require Import DxIntegers DxList64 DxValues DxRegs DxState DxOpcode DxMonad DxFlag DxInstructions DxAST DxMemRegion DxMemType.

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
  DxMemType.Exports
  eval_pc
  upd_pc
  upd_pc_incr
  eval_flag
  upd_flag
  eval_mem_num
  eval_reg
  upd_reg
  eval_mem_regions(*
  add_mem_region
  add_mem_region_ctx*)
  load_mem
  store_mem_imm
  store_mem_reg
  __
  list_get
  get_mem_region
  get_dst
  reg64_to_reg32
  get_src
  get_offset
  get_immediate
  eval_immediate
  get_opcode_ins
  get_opcode_alu64
  get_opcode_alu32
  get_opcode_branch
  get_opcode_mem_ld_imm
  get_opcode_mem_ld_reg
  get_opcode_mem_st_imm
  get_opcode_mem_st_reg
  get_opcode
  get_add
  get_sub
  get_addr_ofs
  is_well_chunk_bool
  check_mem_aux2
  check_mem_aux
  check_mem
  comp_and_0x08_byte
  step_opcode_alu64
  step_opcode_alu32
  step_opcode_branch
  step_opcode_mem_ld_imm
  step_opcode_mem_ld_reg
  step_opcode_mem_st_imm
  step_opcode_mem_st_reg
  step
  bpf_interpreter_aux
  bpf_interpreter
.

Definition dxModuleTest := makeDXModuleWithUserIds 
  [ mem_region_def; state_struct_def]
  [
   "memory_region"; "start_addr"; "block_size"; "block_perm"; "block_ptr";
   "bpf_state"; "state_pc"; "bpf_flag"; "mem_num"; "regsmap"; "mrs"] SymbolIRs.
