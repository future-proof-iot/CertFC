From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.
 

From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
From bpf.src Require Import DxIntegers DxList64 DxValues DxRegs DxState DxOpcode DxMonad DxFlag DxAST DxMemRegion DxMemType DxInstructions.

Open Scope monad_scope.
Fixpoint calc_sum (v: valu32_t) (n:nat){struct n}: M valu32_t :=
  match n with
  | O => returnM val32_zero
  | S n1 =>
    do nv <- get_add v val32_one;
      calc_sum nv n1
  end.

Close Scope monad_scope.

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
  upd_pc_incr
  upd_reg
  upd_flag
  eval_mem_regions
  __
  (**r to test if `Coq list` to `C array` is ok? *)
  list_get
  (**r read memory_region *)
  get_mem_region
  (**r 1. check complex expression in the return statement *)
  get_immediate
  (**r *)
  get_opcode_mem_ld_imm
  (**r the simplest function: a + b *)
  get_add
  (**r 2. check complex expression in the return statement *)
  get_addr_ofs
  (**r check switch-case *)
  is_well_chunk_bool
  (**r complex function: including `get_add` and recursion *)
  calc_sum
  step_opcode_mem_ld_imm
.
(*
Definition dxModuleTest := makeDXModuleWithDefaults SymbolIRs.*)

Definition dxModuleTest := makeDXModuleWithUserIds 
  [ mem_region_def; state_struct_def]
  [
   "memory_region"; "start_addr"; "block_size"; "block_perm"; "block_ptr";
   "bpf_state"; "state_pc"; "bpf_flag"; "mem_num"; "regsmap"; "mrs"] SymbolIRs.