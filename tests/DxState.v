From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

Require Import IdentDef CoqIntegers DxIntegers DxValues DxFlag DxRegs DxMemRegion.

From Coq Require Import List ZArith.
Import ListNotations.

Record state := mkst {
  pc_loc  : int64_t;
  regs_st : regmap;
  flag    : bpf_flag;
  bpf_mrs : memory_regions;
  bpf_m   : Memory.mem;
}.

Definition init_mem: Memory.mem := Memory.Mem.empty.

Definition init_state: state := {|
  pc_loc  := Integers.Int64.zero;
  regs_st := init_regmap;
  flag    := BPF_OK;
  bpf_mrs := default_memory_regions;
  bpf_m   := init_mem;
 |}.

Definition eval_pc (st: state): int64_t := pc_loc st.

Definition upd_pc (p: int64_t) (st:state): state := {|
  pc_loc  := p;
  regs_st := regs_st st;
  flag    := flag st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

(*
Definition upd_pc (p: int64_t) (st:state): state := {|
  pc_loc  := pc_loc st;
  regs_st := regs_st st;
  flag    := flag st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

*)

Definition upd_pc_incr (st:state): state := {|
  pc_loc  := Int64.add (pc_loc st) Int64.one;
  regs_st := regs_st st;
  flag    := flag st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

Definition eval_reg (r: reg) (st:state): val64_t :=
  eval_regmap r (regs_st st).

Definition upd_reg (r:reg) (v:val64_t) (st:state): state := {|
  pc_loc  := pc_loc st;
  regs_st := upd_regmap r v (regs_st st);
  flag    := flag st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

Definition eval_flag (st:state): bpf_flag := flag st.

Definition upd_flag (f: bpf_flag) (st:state): state := {|
  pc_loc  := pc_loc st;
  regs_st := regs_st st;
  flag    := f;
  bpf_mrs := bpf_mrs st;
  bpf_m   := bpf_m st;
|}.

Definition eval_mem (st: state):Mem.mem := bpf_m st.

Definition upd_mem (m: Mem.mem) (st: state): state := {|
  pc_loc  := pc_loc st;
  regs_st := regs_st st;
  flag    := flag st;
  bpf_mrs := bpf_mrs st;
  bpf_m   := m;
|}.

(*
Definition eval_mem_regions (st:state): memory_regions := snd st.

Definition upd_mem_regions (mrs: memory_regions) (st:state): state :=
  let m  := fst (fst (fst st)) in
  let rs := snd (fst (fst st)) in
  let f  := snd (fst st) in
    (m, rs, f, mrs).*)

Definition load_mem (chunk: memory_chunk) (ptr: val64_t) (st: state) :=
  match Mem.loadv chunk (bpf_m st) ptr with
  | Some res => res
  | None => val64_zero
  end.

Definition store_mem_imm (chunk: memory_chunk) (ptr: val64_t) (v: vals32_t) (st: state): state :=
  match Mem.storev chunk (bpf_m st) ptr v with
  | Some m => upd_mem m st
  | None => upd_mem init_mem st
  end.

Definition store_mem_reg (chunk: memory_chunk) (ptr v: val64_t) (st: state): state :=
  match Mem.storev chunk (bpf_m st) ptr v with
  | Some m => upd_mem m st
  | None => upd_mem init_mem st
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
  Ctypes.Composite state_id Ctypes.Struct [(pc_id, C_U32); (regmaps_id, C_regmap); (flag_id, C_S32); (mem_regions_id, mem_regions_type)] Ctypes.noattr.

Definition stateCompilableType := MkCompilableType state state_struct_type.

Module Exports.
  Definition stateCompilableType := stateCompilableType.
End Exports.
