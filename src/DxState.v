From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

From bpf.comm Require Import State.
From bpf.src Require Import IdentDef CoqIntegers DxIntegers DxValues DxFlag DxRegs DxMemRegion DxList64.

From Coq Require Import List ZArith.
Import ListNotations.

(******************** Dx Related *******************)

(** Coq2C: state -> 
            struct state {
              unsigned int pc;
              unsigned long long regmap[11];
            };
  *)

Definition state_struct_type: Ctypes.type := Ctypes.Tstruct state_id Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite state_id Ctypes.Struct [(pc_id, C_U32); (flag_id, C_S32); (regmaps_id, C_regmap); (mem_num_id, C_U32); (mem_regs_id, mem_region_type); (ins_len_id, C_U32); (ins_id, C_U64_pointer)] Ctypes.noattr.

Definition stateCompilableType := MkCompilableType state state_struct_type.

Module Exports.
  Definition stateCompilableType := stateCompilableType.
End Exports.
