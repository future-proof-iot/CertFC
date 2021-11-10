From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

Require Import IdentDef CoqIntegers DxIntegers DxValues DxFlag DxRegs DxMemRegion.

From Coq Require Import List ZArith.
Import ListNotations.

Record state := mkbst{
  pc_loc : int64_t;
  regs   : regmap;
  flag   : bpf_flag;
  mrs    : memory_regions;
}.

Definition init_state: state := {|
  pc_loc := Integers.Int64.zero;
  regs   := init_regmap;
  flag   := BPF_OK;
  mrs    := default_memory_regions;
|}.

Definition eval_pc (st: state): int64_t := pc_loc st.

Definition upd_pc (p: int64_t) (st:state): state := {|
  pc_loc := p;
  regs   := regs st;
  flag   := flag st;
  mrs    := mrs st;
|}.

Definition upd_pc_incr (st:state): state := {|
  pc_loc := Int64.add (pc_loc st) Int64.one;
  regs   := regs st;
  flag   := flag st;
  mrs    := mrs st;
|}.

Definition eval_reg (r: reg) (st:state): val64_t :=
  eval_regmap r (regs st).

Definition upd_reg (r:reg) (v:val64_t) (st:state): state := {|
  pc_loc := pc_loc st;
  regs   := upd_regmap r v (regs st);
  flag   := flag st;
  mrs    := mrs st;
|}.

Definition eval_flag (st:state): bpf_flag := flag st.

Definition upd_flag (f: bpf_flag) (st:state): state := {|
  pc_loc := pc_loc st;
  regs   := regs st;
  flag   := f;
  mrs    := mrs st;
|}.

Definition eval_mem_regions (st:state): memory_regions := mrs st.

Definition upd_mem_regions (mrs1: memory_regions) (st:state): state := {|
  pc_loc := pc_loc st;
  regs   := regs st;
  flag   := flag st;
  mrs    := mrs1;
|}.

(******************** Dx Related *******************)

(** Coq2C: state -> 
            struct state {
              unsigned int pc;
              unsigned long long regmap[11];
            };
  *)

Definition state_struct_type: Ctypes.type := Ctypes.Tpointer (Ctypes.Tstruct state_id Ctypes.noattr) Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(pc_id, C_U32); (regmaps_id, C_regmap); (flag_id, C_S32); (mem_regions_id, mem_regions_type)] Ctypes.noattr.

Definition stateCompilableType := MkCompilableType state state_struct_type.
(** Type for state -> val64_t *)
Definition mem_regionToVal64CompilableSymbolType :=
  MkCompilableSymbolType [mem_regionCompilableType] (Some val64CompilableType).

Definition Const_block_ptr := 
  MkPrimitive mem_regionToVal64CompilableSymbolType 
              block_ptr
              (fun es => match es with
                         | [e1] => Ok (C_U64_one)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition stateCompilableType := stateCompilableType.
End Exports.
