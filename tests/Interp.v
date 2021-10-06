From Coq Require Import List.
Import ListNotations.
From compcert Require Import Coqlib Integers AST Ctypes Values.
From dx.tests Require Import Int16 Asm Sem Monad.

Definition get_reg (i:nat):option reg :=
  match i with
  | 0%nat  => Some R0
  | 1%nat  => Some R1
  | 2%nat  => Some R2
  | 3%nat  => Some R3
  | 4%nat  => Some R4
  | 5%nat  => Some R5
  | 6%nat  => Some R6
  | 7%nat  => Some R7
  | 8%nat  => Some R8
  | 9%nat  => Some R9
  | 10%nat => Some R10
  | _      => None
  end.

Definition get_instruction (opcode:nat) (rd rs:reg) (o: int16) (i:int):instruction+bpf_flag :=
  match opcode with
  (*ALU64*)
  | 0x07%nat => inl (BPF_ADD64i rd i)
  | 0x0f%nat => inl (BPF_ADD64r rd rs)
  | 0x87%nat => inl (BPF_NEG64  rd)
  (*ALU32*)
  | 0x04%nat => inl (BPF_ADD32i rd i)
  | 0x0c%nat => inl (BPF_ADD32r rd rs)
  | 0x84%nat => inl (BPF_NEG32  rd)
  | 0x95%nat => inl BPF_RET

  | _        => inr BPF_ILLEGAL_INSTRUCTION
  end.

Definition decode' (i: int64): instruction+bpf_flag :=
  let n_opcode:nat := get_opcode i in
  let n_dst:nat  := get_dst i in
  let n_src:nat  := get_src i in
  let n_offset:int16 := get_offset i in
  let n_immediate:int := get_immediate i in
    match (get_reg n_dst), (get_reg n_src) with
    | Some rd, Some rs =>
      get_instruction n_opcode rd rs n_offset n_immediate
    | _, _             => inr BPF_ILLEGAL_INSTRUCTION
    end.

Definition decode (l: list int64) (n:nat): instruction+bpf_flag :=
  let n_val:option int64 := nth_error l n in
  match n_val with
  | Some nv => decode' nv
  | None    => inr BPF_ILLEGAL_LEN
  end.

Open Scope monad_scope.

Fixpoint interpreter (fuel:nat) (l:list int64): MrBPF unit :=
  match fuel with
  | O => upd_errorundef (ErrorL BPF_ILLEGAL_LEN)
  | S n => 
    do pc <- eval_pc;
    match (decode l pc) with
    | inl ins => do _ <- step ins (nth_error l (pc+1)) ; interpreter n l
    | inr f   => upd_errorundef (ErrorL f)
    end
  end.

Close Scope monad_scope.