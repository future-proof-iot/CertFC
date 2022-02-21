From bpf.comm Require Import rBPFAST List64 MemRegion Regs State Monad Flag.

From bpf.monadicmodel Require Import Opcode.

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.proof Require Import CommonLib.

Open Scope Z_scope.

Definition int64_correct (x:int64) (v: val) :=
  Vlong x = v.

Definition val64_correct (x:val) (v: val) :=
  x = v /\ exists vl, x = Vlong vl.

Definition valu32_correct (x:val) (v: val) :=
  x = v /\ exists vi, x = Vint vi.

Definition val_ptr_correct (x:val) (v: val) :=
  x = v /\ exists b ofs, x = Vptr b ofs.

Definition val_ptr_null_correct (x:val) (v: val) (st: State.state) (m: Mem.mem) :=
  x = v /\ ((exists b ofs, x = Vptr b ofs) \/ x = Vnullptr).

Definition addr_valu32_correct (x:val) (v: val) :=
  x = v /\ exists b ofs, x = Vptr b ofs.

Definition sint32_correct (x: int) (v: val) :=
  Vint x = v.

Definition nat8_correct (x: nat) (v: val) :=
  Vint (Int.repr (Z.of_nat x)) = v.

Definition nat_correct (x: nat) (v: val) :=
  Vint (Int.repr (Z.of_nat x)) = v /\
    (* Avoid overflow *)
    Int.unsigned (Int.repr (Z.of_nat x)) = Z.of_nat x.

Definition reg_correct (r: reg) (v: val) :=
  (*complu_lt_32 v (Vint (Int.repr 11)) = true /\ (**r ensured by verifier *) *)
    v = Vint (Int.repr (id_of_reg r)).


Definition reg_int64_correct (x:int64) (v: val) :=
  Vlong x = v /\
    0 <= (Int64.unsigned (Int64.shru (Int64.and x (Int64.repr 4095)) (Int64.repr 8))) <= 10.

Open Scope nat_scope.

Definition opcode_and_07_correct (x: nat) (v: val) :=
   Vint (Int.repr (Z.of_nat x)) = v /\ (x <= 255) /\ (Nat.land x 0x07%nat = 0x07%nat).
(*
Definition is_illegal_alu64_ins (i:nat): Prop :=
  ((Nat.land i 240) <> 0x00) /\
  ((Nat.land i 240) <> 0x10) /\
  ((Nat.land i 240) <> 0x20) /\
  ((Nat.land i 240) <> 0x30) /\
  ((Nat.land i 240) <> 0x40) /\
  ((Nat.land i 240) <> 0x50) /\
  ((Nat.land i 240) <> 0x60) /\
  ((Nat.land i 240) <> 0x70) /\
  (((Nat.land i 240) = 0x80) -> (i <> 0x87)) /\
  ((Nat.land i 240) <> 0x90) /\
  ((Nat.land i 240) <> 0xa0) /\
  ((Nat.land i 240) <> 0xb0) /\
  ((Nat.land i 240) <> 0xc0). *)

(*
Definition is_illegal_alu64_ins (i:nat): Prop :=
  i <> 0x07 /\ i <> 0x0f /\
  i <> 0x17 /\ i <> 0x1f /\
  i <> 0x27 /\ i <> 0x2f /\
  i <> 0x37 /\ i <> 0x3f /\
  i <> 0x47 /\ i <> 0x4f /\
  i <> 0x57 /\ i <> 0x5f /\
  i <> 0x67 /\ i <> 0x6f /\
  i <> 0x77 /\ i <> 0x7f /\
  i <> 0x87 /\
  i <> 0x97 /\ i <> 0x9f /\
  i <> 0xa7 /\ i <> 0xaf /\
  i <> 0xb7 /\ i <> 0xbf /\
  i <> 0xc7 /\ i <> 0xcf.
   *)


Definition is_illegal_alu64_ins (i:nat): Prop :=
  ((Nat.land i 240) <> 0x00) /\
  ((Nat.land i 240) <> 0x10) /\
  ((Nat.land i 240) <> 0x20) /\
  ((Nat.land i 240) <> 0x30) /\
  ((Nat.land i 240) <> 0x40) /\
  ((Nat.land i 240) <> 0x50) /\
  ((Nat.land i 240) <> 0x60) /\
  ((Nat.land i 240) <> 0x70) /\
  ((Nat.land i 240) <> 0x80) /\
  ((Nat.land i 240) <> 0x90) /\
  ((Nat.land i 240) <> 0xa0) /\
  ((Nat.land i 240) <> 0xb0) /\
  ((Nat.land i 240) <> 0xc0).


Definition opcode_alu64_correct (opcode: opcode_alu64) (v: val) :=
  match opcode with
  | op_BPF_ADD64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x07 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x0f 240)))
  | op_BPF_SUB64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x17 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x1f 240)))
  | op_BPF_MUL64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x27 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x2f 240)))
  | op_BPF_DIV64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x37 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x3f 240)))
  | op_BPF_OR64  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x47 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x4f 240)))
  | op_BPF_AND64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x57 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x5f 240)))
  | op_BPF_LSH64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x67 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x6f 240)))
  | op_BPF_RSH64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x77 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x7f 240)))
  | op_BPF_NEG64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x87 240)))
  | op_BPF_MOD64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x97 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x9f 240)))
  | op_BPF_XOR64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xa7 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xaf 240)))
  | op_BPF_MOV64 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xb7 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xbf 240)))
  | op_BPF_ARSH64=> v = Vint (Int.repr (Z.of_nat (Nat.land 0xc7 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xcf 240))) (*
  | op_BPF_ALU64_ILLEGAL_INS => exists i, v = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\ is_illegal_alu64_ins i *)
  | op_BPF_ALU64_ILLEGAL_INS => exists i, v = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\ is_illegal_alu64_ins i
  end.

Definition is_illegal_alu32_ins (i:nat): Prop :=
  ((Nat.land i 240) <> 0x00) /\
  ((Nat.land i 240) <> 0x10) /\
  ((Nat.land i 240) <> 0x20) /\
  ((Nat.land i 240) <> 0x30) /\
  ((Nat.land i 240) <> 0x40) /\
  ((Nat.land i 240) <> 0x50) /\
  ((Nat.land i 240) <> 0x60) /\
  ((Nat.land i 240) <> 0x70) /\
  ((Nat.land i 240) <> 0x80) /\
  ((Nat.land i 240) <> 0x90) /\
  ((Nat.land i 240) <> 0xa0) /\
  ((Nat.land i 240) <> 0xb0) /\
  ((Nat.land i 240) <> 0xc0).

Definition opcode_alu32_correct (opcode: opcode_alu32) (v: val) :=
  match opcode with
  | op_BPF_ADD32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x04 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x0c 240)))
  | op_BPF_SUB32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x14 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x1c 240)))
  | op_BPF_MUL32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x24 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x2c 240)))
  | op_BPF_DIV32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x34 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x3c 240)))
  | op_BPF_OR32  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x44 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x4c 240)))
  | op_BPF_AND32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x54 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x5c 240)))
  | op_BPF_LSH32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x64 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x6c 240)))
  | op_BPF_RSH32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x74 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x7c 240)))
  | op_BPF_NEG32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x84 240)))
  | op_BPF_MOD32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0x94 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x9c 240)))
  | op_BPF_XOR32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xa4 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xac 240)))
  | op_BPF_MOV32 => v = Vint (Int.repr (Z.of_nat (Nat.land 0xb4 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xbc 240)))
  | op_BPF_ARSH32=> v = Vint (Int.repr (Z.of_nat (Nat.land 0xc4 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xcc 240)))
  | op_BPF_ALU32_ILLEGAL_INS => exists i, v = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\ is_illegal_alu32_ins i
  end.

Definition is_illegal_jmp_ins (i:nat): Prop :=
  ((Nat.land i 240) <> 0x00) /\
  ((Nat.land i 240) <> 0x10) /\
  ((Nat.land i 240) <> 0x20) /\
  ((Nat.land i 240) <> 0x30) /\
  ((Nat.land i 240) <> 0x40) /\
  ((Nat.land i 240) <> 0x50) /\
  ((Nat.land i 240) <> 0x60) /\
  ((Nat.land i 240) <> 0x70) /\
  ((Nat.land i 240) <> 0x80) /\
  ((Nat.land i 240) <> 0x90) /\
  ((Nat.land i 240) <> 0xa0) /\
  ((Nat.land i 240) <> 0xb0) /\
  ((Nat.land i 240) <> 0xc0) /\
  ((Nat.land i 240) <> 0xd0).

Definition opcode_branch_correct (opcode: opcode_branch) (v: val) :=
  match opcode with
  | op_BPF_JA    => v = Vint (Int.repr (Z.of_nat (Nat.land 0x05 240)))
  | op_BPF_JEQ   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x15 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x1d 240)))
  | op_BPF_JGT   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x25 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x2d 240)))
  | op_BPF_JGE   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x35 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x3d 240)))
  | op_BPF_JLT   => v = Vint (Int.repr (Z.of_nat (Nat.land 0xa5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xad 240)))
  | op_BPF_JLE   => v = Vint (Int.repr (Z.of_nat (Nat.land 0xb5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xbd 240)))
  | op_BPF_JSET  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x45 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x4d 240)))
  | op_BPF_JNE   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x55 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x5d 240)))
  | op_BPF_JSGT  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x65 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x6d 240)))
  | op_BPF_JSGE  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x75 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0x7d 240)))
  | op_BPF_JSLT  => v = Vint (Int.repr (Z.of_nat (Nat.land 0xc5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xcd 240)))
  | op_BPF_JSLE  => v = Vint (Int.repr (Z.of_nat (Nat.land 0xd5 240))) \/ v = Vint (Int.repr (Z.of_nat (Nat.land 0xdd 240)))
  | op_BPF_CALL  => v = Vint (Int.repr (Z.of_nat (Nat.land 0x85 240)))
  | op_BPF_RET   => v = Vint (Int.repr (Z.of_nat (Nat.land 0x95 240)))
  | op_BPF_JMP_ILLEGAL_INS => exists i, v = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\ is_illegal_jmp_ins i
  end.


Close Scope nat_scope.



Definition opcode_mem_ld_imm_correct (opcode: opcode_mem_ld_imm) (v: val) :=
  match opcode with
  | op_BPF_LDDW => exists vi, v = Vint vi (**this one is too weak, but for current proof, it is enough *)
  | op_BPF_LDX_IMM_ILLEGAL_INS => exists vi, v = Vint vi (*v = Vundef*)
  end.

Definition MyListType_correct (b:block) (len: nat) (l: MyListType) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
  v = Vptr b Ptrofs.zero /\
    forall pc, 0 <= Z.of_nat pc < Z.of_nat len ->
    exists vl,
        List.nth_error l  pc = Some vl /\
        Mem.loadv Mint64 m (Vptr b (Ptrofs.repr (8 * (Z.of_nat pc)))) = Some (Vlong vl)
.

Definition pc_correct (x: nat) (v: val) (st: State.state) (m:Memory.Mem.mem) :=
  Vint (Int.repr (Z.of_nat x)) = v /\  0 <= Z.of_nat x < Z.of_nat (mrs_num st) /\ 0 <= 8 * Z.of_nat (mrs_num st) <= Ptrofs.max_unsigned. (**r the number of input instructions should be less than Ptrofs.max_unsigned *)

Definition ins_idx_correct (x: int) (v: val) (st: State.state) (m:Memory.Mem.mem) :=
  Vint x = v /\
  0 <= Int.signed x < Z.of_nat (ins_len st).


Definition len_correct (len: nat) (x: int) (v: val) :=
  Vint x = v /\  Int.signed x = Z.of_nat len.

Definition match_chunk (x : memory_chunk) (b: val) :=
  b = memory_chunk_to_valu32 x.

Definition flag_correct (f: bpf_flag) (v: val) :=
  v = Vint (int_of_flag f).

Definition perm_correct (p: permission) (n: val): Prop :=
  match p with
  | Freeable => n = Vint (Int.repr 3)
  | Writable => n = Vint (Int.repr 2)
  | Readable => n = Vint (Int.repr 1)
  | Nonempty => n = Vint (Int.repr 0)
  end.

Definition correct_perm (p: permission) (n: int): Prop :=
  match p with
  | Freeable => n = Int.repr 3
  | Writable => n = Int.repr 2
  | Readable => n = Int.repr 1
  | Nonempty => n = Int.repr 0
  end.

(**r just a copy from clightlogic *)
Definition match_bool (b:bool) (v:val) :=
  v = Vint (if b then Integers.Int.one else Integers.Int.zero).

Close Scope Z_scope.