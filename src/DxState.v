From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

From bpf.src Require Import IdentDef CoqIntegers DxIntegers DxValues DxFlag DxRegs DxMemRegion.

From Coq Require Import List ZArith.
Import ListNotations.

Record state := mkst {
  pc_loc  : sint32_t;  (**r should pc_loc be u32 or s32: because ofs is s16, res = pc_loc+ofs may be negative! we should test res before calculating *)
  flag    : bpf_flag;
  regs_st : regmap;
  mrs_num : nat;  (**r number of memory regions, put it here to guarantee align *)
  bpf_mrs : MyMemRegionsType;
  bpf_m   : Memory.mem;
}.

Definition init_mem: Memory.mem := Memory.Mem.empty.

Definition init_state: state := {|
  pc_loc  := Int.zero;
  flag    := BPF_OK;
  regs_st := init_regmap;
  mrs_num := 0;
  bpf_mrs := default_memory_regions;
  bpf_m   := init_mem;
 |}.

Definition eval_pc (st: state): sint32_t := pc_loc st.

Definition upd_pc (p: sint32_t) (st:state): state := {|
  pc_loc  := p;
  flag    := flag st;
  regs_st := regs_st st;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

Definition upd_pc_incr (st:state): state := {|
  pc_loc  := Int.add (pc_loc st) Int.one;
  flag    := flag st;
  regs_st := regs_st st;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

Definition eval_flag (st:state): bpf_flag := flag st.

Definition upd_flag (f: bpf_flag) (st:state): state := {|
  pc_loc  := pc_loc st;
  flag    := f;
  regs_st := regs_st st;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

Definition eval_mem_num (st:state): nat := (mrs_num st). (**r uint32_t -> nat*)

(*
Definition upd_mem_num_incr (st:state): state := {|
  pc_loc  := pc_loc st;
  flag    := flag st;
  mem_num := Int.add (mem_num st) Int.one;
  regs_st := regs_st st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.*)

Definition eval_reg (r: reg) (st:state): val64_t :=
  eval_regmap r (regs_st st).

Definition upd_reg (r:reg) (v:val64_t) (st:state): state := {|
  pc_loc  := pc_loc st;
  flag    := flag st;
  regs_st := upd_regmap r v (regs_st st);
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

Definition eval_mem_regions (st:state): MyMemRegionsType := bpf_mrs st.
(*
Definition add_mem_region (mr: memory_region) (st:state): state :={|
  pc_loc  := pc_loc st;
  flag    := flag st;
  mem_num := Int.add (mem_num st) Int.one;
  regs_st := regs_st st;
  bpf_mrs := MyMemRegionsAdd mr (bpf_mrs st);
  bpf_m   := bpf_m st;
|}.

Definition add_mem_region_ctx (mr: memory_region) (st:state): state :={|
  pc_loc  := pc_loc st;
  flag    := flag st;
  mem_num := Int.one;
  regs_st := regs_st st;
  bpf_mrs := MyMemRegionsAdd mr (bpf_mrs st);
  bpf_m   := bpf_m st;
|}.
*)
Definition eval_mem (st: state):Mem.mem := bpf_m st.

Definition upd_mem (m: Mem.mem) (st: state): state := {| (**r never be used I guess *)
  pc_loc  := pc_loc st;
  flag    := flag st;
  regs_st := regs_st st;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := m;
|}.

Definition load_mem (chunk: memory_chunk) (ptr: valu32_t) (st: state) :=
  match ptr with
  | Vptr b ofs =>
    match Mem.load chunk (bpf_m st) b (Ptrofs.unsigned ofs) with
    | Some res => res
    | None => val64_zero
    end
  | _ => val64_zero
  end.

Definition store_mem_imm (chunk: memory_chunk) (ptr: valu32_t) (v: vals32_t) (st: state): state :=
  match ptr with
  | Vptr b ofs =>
    match Mem.store chunk (bpf_m st) b (Ptrofs.unsigned ofs) v with
    | Some m => upd_mem m st
    | None => upd_flag BPF_ILLEGAL_MEM st
    end
  | _ => upd_flag BPF_ILLEGAL_MEM st
  end.

Definition store_mem_reg (chunk: memory_chunk) (ptr: valu32_t) (v: val64_t) (st: state): state :=
  match ptr with
  | Vptr b ofs =>
    match Mem.store chunk (bpf_m st) b (Ptrofs.unsigned ofs) v with
    | Some m => upd_mem m st
    | None => upd_flag BPF_ILLEGAL_MEM st
    end
  | _ => upd_flag BPF_ILLEGAL_MEM st
  end.

(******************** Dx Related *******************)

(** Coq2C: state -> 
            struct state {
              unsigned int pc;
              unsigned long long regmap[11];
            };
  *)

Definition state_struct_type: Ctypes.type := Ctypes.Tstruct state_id Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(pc_id, C_U32); (flag_id, C_S32); (regmaps_id, C_regmap); (mem_regs_id, mem_region_type); (mem_num_id, C_U32)] Ctypes.noattr.

Definition stateCompilableType := MkCompilableType state state_struct_type.

Module Exports.
  Definition stateCompilableType := stateCompilableType.
End Exports.
