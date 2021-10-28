From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values Memory.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

Require Import IdentDef CoqIntegers DxIntegers DxValues DxFlag DxRegs DxMemRegion.

From Coq Require Import List ZArith.
Import ListNotations.

Record regs_state: Type := make_rst{
  pc_loc  : int64_t;
  regs_st : regmap;
}.

Definition state: Type := Memory.mem * regs_state * bpf_flag * memory_regions.

Definition init_mem: Memory.mem := Memory.Mem.empty.

Definition init_regs_state := {| pc_loc := Integers.Int64.zero; regs_st := init_regmap;|}.

Definition init_state: state := 
  (init_mem, init_regs_state, BPF_OK, default_memory_regions).

Definition eval_pc_tot (st: state): int64_t := pc_loc (snd (fst (fst st))).

Definition upd_pc_tot (p: int64_t) (st:state): state :=
  let m  := fst (fst (fst st)) in
  let rs := snd (fst (fst st)) in
  let f  := snd (fst st) in
  let mrs:= snd st in
  let next_rs := {| pc_loc := p; regs_st := regs_st rs; |} in
    (m, next_rs, f, mrs).

Definition upd_pc_incr_tot (st:state): state :=
  let m  := fst (fst (fst st)) in
  let rs := snd (fst (fst st)) in
  let f  := snd (fst st) in
  let mrs:= snd st in
  let next_rs := {| pc_loc := Int64.add (pc_loc rs) Int64.one; regs_st := regs_st rs; |} in
    (m, next_rs, f, mrs).

Definition eval_reg_tot (r: reg) (st:state): val64_t :=
  eval_regmap r (regs_st (snd (fst (fst st)))).

Definition upd_reg_tot (r:reg) (v:val64_t) (st:state): state :=
  let m  := fst (fst (fst st)) in
  let rs := snd (fst (fst st)) in
  let f  := snd (fst st) in
  let mrs:= snd st in
  let next_rs := {| pc_loc := pc_loc rs; regs_st := upd_regmap r v (regs_st rs); |} in
    (m, next_rs, f, mrs).

Definition eval_flag_tot (st:state): bpf_flag := snd (fst st).

Definition upd_flag_tot (f: bpf_flag) (st:state): state :=
  let m  := fst (fst (fst st)) in
  let rs := snd (fst (fst st)) in
  let mrs:= snd st in
    (m, rs, f, mrs).

Definition eval_mem_regions_tot (st:state): memory_regions := snd st.

Definition upd_mem_regions_tot (mrs: memory_regions) (st:state): state :=
  let m  := fst (fst (fst st)) in
  let rs := snd (fst (fst st)) in
  let f  := snd (fst st) in
    (m, rs, f, mrs).

(** Coq2C: state -> 
            struct state {
              unsigned int pc;
              unsigned long long regmap[11];
            };
  *)

Definition state_struct_type: Ctypes.type := Ctypes.Tstruct state_id Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(pc_id, C_U32); (regmaps_id, C_regmap); (mem_regions_id, mem_regions_type)] Ctypes.noattr.

(*
Definition regsMatchableType := MkCompilableType regs_state state_struct_type.*)

Definition stateCompilableType := MkCompilableType state state_struct_type.

(*
(** Type signature: reg -> val64_t -> state -> state
  *)
Definition regToVal64ToStateToStateSymbolType :=
  MkCompilableSymbolType [regCompilableType; val64CompilableType; stateCompilableType] (Some stateCompilableType).

Definition Const_upd_reg_tot :=
  MkPrimitive regToVal64ToStateToStateSymbolType
                upd_reg_tot
                (fun es => match es with
                           | [r; v; st] => Ok (
                              Csyntax.Eassign
                              (Csyntax.Eindex st r C_U64)
                              (Csyntax.Evalof v C_U64)
                              C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end). *)

Module Exports.
  Definition stateCompilableType := stateCompilableType. (*
  Definition Const_upd_reg_tot := Const_upd_reg_tot.*)
End Exports.