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
  upd_flag
  eval_mem_regions
  upd_mem_regions
  load_mem
  store_mem_imm
  store_mem_reg
  __
  list_get
  get_dst
  reg64_to_reg32
  get_src
  get_offset
  eval_offset
  get_immediate
  eval_immediate
  get_opcode_alu64_imm
  get_opcode_alu64_reg
  get_opcode_alu32_imm
  get_opcode_alu32_reg
  get_opcode_branch_imm
  get_opcode_branch_reg
  get_opcode_mem_ld_imm
  get_opcode_mem_ld_reg
  get_opcode_mem_st_imm
  get_opcode_mem_st_reg
  get_opcode
  get_addl
  get_subl
  getMemRegion_block_ptr
  getMemRegion_start_addr
  getMemRegion_block_size
  is_well_chunk_bool
  check_mem_aux
  check_mem
  step_opcode_alu64_imm
  step_opcode_alu64_reg
  step_opcode_alu32_imm
  step_opcode_alu32_reg
  step_opcode_branch_imm
  step_opcode_branch_reg
  step_opcode_mem_ld_imm
  step_opcode_mem_ld_reg
  step_opcode_mem_st_imm
  step_opcode_mem_st_reg
  step
  bpf_interpreter_aux
  bpf_interpreter
.
(*
Definition dxModuleTest := makeDXModuleWithDefaults SymbolIRs. *)

Definition dxModuleTest := makeDXModuleWithUserIds 
  [ mem_region_def; mem_regions_def; state_struct_def]
  [
   "memory_region"; "start_addr"; "block_size"; "block_ptr";
   "memory_regions"; "bpf_ctx"; "bpf_stk"; "content";
   "bpf_state"; "state_pc"; "regsmap"; "bpf_flag"; "mrs"] SymbolIRs.
