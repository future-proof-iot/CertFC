From bpf.src Require Import DxIntegers DxValues DxOpcode DxMemRegion DxRegs DxState DxMonad DxFlag.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState.

Open Scope Z_scope.

Definition int64_correct (x:int64_t) (v: val) :=
  Vlong x = v.

Definition val64_correct (x:val64_t) (v: val) :=
  x = v /\ exists vl, x = Vlong vl.

Definition valu32_correct (x:valu32_t) (v: val) :=
  x = v /\ exists vi, x = Vint vi.

Definition sint32_correct (x: sint32_t) (v: val) :=
  Vint x = v.

Definition int8_correct (x: int8_t) (v: val) :=
  Vint (Int.repr (Byte.unsigned x)) = v.

Definition nat_correct (x: nat) (v: val) :=
  Vint (Int.repr (Z.of_nat x)) = v.

Definition reg_correct (r: reg) (v: val) :=
  (*complu_lt_32 v (Vint (Int.repr 11)) = true /\ (**r ensured by verifier *) *)
    v = Vint (Int.repr (id_of_reg r)).

Definition reg_int64_correct (x:int64_t) (v: val) :=
  Vlong x = v /\
    0 <= (Int64.unsigned (Int64.shru (Int64.and x (Int64.repr 4095)) (Int64.repr 8))) <= 10.

Definition opcode_mem_ld_imm_correct (opcode: opcode_mem_ld_imm) (v: val) :=
  match opcode with
  | op_BPF_LDDW => exists vi, v = Vint vi (**this one is too weak, but for current proof, it is enough *)
  | op_BPF_LDX_IMM_ILLEGAL_INS => exists vi, v = Vint vi (*v = Vundef*)
  end.

Definition match_chunk (x : memory_chunk) (b: val) :=
  b = Vint (
          match x with
          | Mint8unsigned => Integers.Int.one
          | Mint16unsigned => Integers.Int.repr 2
          | Mint32 => Integers.Int.repr 4
          | Mint64 => Integers.Int.repr 8
          | _ => Integers.Int.repr 0
          end).

Definition flag_correct (f: bpf_flag) (v: val) :=
  v = Vint (int_of_flag f).

Close Scope Z_scope.