From bpf.src Require Import DxIntegers DxValues DxAST DxList64 DxOpcode DxMemRegion DxRegs DxState DxMonad DxFlag.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.proof Require Import CommonLib.

Open Scope Z_scope.

Definition int64_correct (x:int64_t) (v: val) :=
  Vlong x = v.

Definition val64_correct (x:val64_t) (v: val) :=
  x = v /\ exists vl, x = Vlong vl.

Definition valu32_correct (x:valu32_t) (v: val) :=
  x = v /\ exists vi, x = Vint vi.

Definition val_ptr_correct (x:valu32_t) (v: val) :=
  x = v /\ exists b ofs, x = Vptr b ofs.

Definition addr_valu32_correct (x:valu32_t) (v: val) :=
  x = v /\ exists b ofs, x = Vptr b ofs.

Definition sint32_correct (x: sint32_t) (v: val) :=
  Vint x = v.

Definition int8_correct (x: int8_t) (v: val) :=
  Vint (Int.repr (Byte.unsigned x)) = v.

Definition nat_correct (x: nat) (v: val) :=
  Vint (Int.repr (Z.of_nat x)) = v /\
    (* Avoid overflow *)
    Int.unsigned (Int.repr (Z.of_nat x)) = Z.of_nat x.

Definition reg_correct (r: reg) (v: val) :=
  (*complu_lt_32 v (Vint (Int.repr 11)) = true /\ (**r ensured by verifier *) *)
    v = Vint (Int.repr (id_of_reg r)).


Definition reg_int64_correct (x:int64_t) (v: val) :=
  Vlong x = v /\
    0 <= (Int64.unsigned (Int64.shru (Int64.and x (Int64.repr 4095)) (Int64.repr 8))) <= 10.

Definition opcode_alu64_correct (opcode: opcode_alu64) (v: val) :=
  match opcode with
  | op_BPF_ADD64 => v = Vint (Int.repr 0)
  | op_BPF_SUB64
  | op_BPF_MUL64
  | op_BPF_DIV64
  | op_BPF_OR64
  | op_BPF_AND64
  | op_BPF_LSH64
  | op_BPF_RSH64
  | op_BPF_NEG64
  | op_BPF_MOD64
  | op_BPF_XOR64
  | op_BPF_MOV64
  | op_BPF_ARSH64 => exists vi, v = Vint vi
  | op_BPF_ALU64_ILLEGAL_INS => exists vi, v = Vint vi
  end.

Definition opcode_mem_ld_imm_correct (opcode: opcode_mem_ld_imm) (v: val) :=
  match opcode with
  | op_BPF_LDDW => exists vi, v = Vint vi (**this one is too weak, but for current proof, it is enough *)
  | op_BPF_LDX_IMM_ILLEGAL_INS => exists vi, v = Vint vi (*v = Vundef*)
  end.

Definition MyListType_correct (b:block) (len: nat) (l: MyListType) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  v = Vptr b Ptrofs.zero /\
    forall pc, 0 <= Z.of_nat pc < Z.of_nat len ->
    exists vl,
        List.nth_error l  pc = Some vl /\
        Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (8 * (Z.of_nat pc)))) = Some (Vlong vl)
.

Definition pc_correct (len: nat) (x: sint32_t) (v: val) :=
  Vint x = v /\  0 <= Int.signed x < Z.of_nat len /\ 0 <= 8 * Z.of_nat len <= Ptrofs.max_unsigned. (**r the number of input instructions should be less than Ptrofs.max_unsigned *)


Definition len_correct (len: nat) (x: sint32_t) (v: val) :=
  Vint x = v /\  Int.signed x = Z.of_nat len.

Definition match_chunk (x : memory_chunk) (b: val) :=
  b = memory_chunk_to_valu32 x.

Definition flag_correct (f: bpf_flag) (v: val) :=
  v = Vint (int_of_flag f).

Definition correct_perm (p: permission) (n: int): Prop :=
  match p with
  | Freeable => n = int32_3
  | Writable => n = int32_2
  | Readable => n = int32_1
  | Nonempty => n = int32_0
  end.

(**r just a copy from clightlogic *)
Definition match_bool (b:bool) (v:val) :=
  v = Vint (if b then Integers.Int.one else Integers.Int.zero).

Close Scope Z_scope.