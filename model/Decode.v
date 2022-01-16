From compcert Require Import Integers Values AST Ctypes.
From Coq Require Import ZArith.

From bpf.comm Require Import Int16 Flag Regs rBPFValues.
From bpf.model Require Import Syntax.

(** Overview:
    This module is used to translate `int64` binary code to bpf instructions~ Normally a bpf instruction has opcode+dst+src+offset+immedate.
  *)
Open Scope nat_scope.

Definition get_instruction (opcode:nat) (rd rs:reg) (ofs: int) (i: int): instruction :=
  match opcode with
  (*ALU64*)
  | 0x07 => BPF_BINARY A64 BPF_ADD  rd (inr i)
  | 0x0f => BPF_BINARY A64 BPF_ADD  rd (inl rs)
  | 0x17 => BPF_BINARY A64 BPF_SUB  rd (inr i)
  | 0x1f => BPF_BINARY A64 BPF_SUB  rd (inl rs)
  | 0x27 => BPF_BINARY A64 BPF_MUL  rd (inr i)
  | 0x2f => BPF_BINARY A64 BPF_MUL  rd (inl rs)
  | 0x37 => BPF_BINARY A64 BPF_DIV  rd (inr i)
  | 0x3f => BPF_BINARY A64 BPF_DIV  rd (inl rs)
  | 0x47 => BPF_BINARY A64 BPF_OR   rd (inr i)
  | 0x4f => BPF_BINARY A64 BPF_OR   rd (inl rs)
  | 0x57 => BPF_BINARY A64 BPF_AND  rd (inr i)
  | 0x5f => BPF_BINARY A64 BPF_AND  rd (inl rs)
  | 0x67 => BPF_BINARY A64 BPF_LSH  rd (inr i)
  | 0x6f => BPF_BINARY A64 BPF_LSH  rd (inl rs)
  | 0x77 => BPF_BINARY A64 BPF_RSH  rd (inr i)
  | 0x7f => BPF_BINARY A64 BPF_RSH  rd (inl rs)
  | 0x87 => BPF_NEG A64 rd
  | 0x97 => BPF_BINARY A64 BPF_MOD  rd (inr i)
  | 0x9f => BPF_BINARY A64 BPF_MOD  rd (inl rs)
  | 0xa7 => BPF_BINARY A64 BPF_XOR  rd (inr i)
  | 0xaf => BPF_BINARY A64 BPF_XOR  rd (inl rs)
  | 0xb7 => BPF_BINARY A64 BPF_MOV  rd (inr i)
  | 0xbf => BPF_BINARY A64 BPF_MOV  rd (inl rs)
  | 0xc7 => BPF_BINARY A64 BPF_ARSH rd (inr i)
  | 0xcf => BPF_BINARY A64 BPF_ARSH rd (inl rs)
  (*ALU32*)
  | 0x04 => BPF_BINARY A32 BPF_ADD  rd (inr i)
  | 0x0c => BPF_BINARY A32 BPF_ADD  rd (inl rs)
  | 0x14 => BPF_BINARY A32 BPF_SUB  rd (inr i)
  | 0x1c => BPF_BINARY A32 BPF_SUB  rd (inl rs)
  | 0x24 => BPF_BINARY A32 BPF_MUL  rd (inr i)
  | 0x2c => BPF_BINARY A32 BPF_MUL  rd (inl rs)
  | 0x34 => BPF_BINARY A32 BPF_DIV  rd (inr i)
  | 0x3c => BPF_BINARY A32 BPF_DIV  rd (inl rs)
  | 0x44 => BPF_BINARY A32 BPF_OR   rd (inr i)
  | 0x4c => BPF_BINARY A32 BPF_OR   rd (inl rs)
  | 0x54 => BPF_BINARY A32 BPF_AND  rd (inr i)
  | 0x5c => BPF_BINARY A32 BPF_AND  rd (inl rs)
  | 0x64 => BPF_BINARY A32 BPF_LSH  rd (inr i)
  | 0x6c => BPF_BINARY A32 BPF_LSH  rd (inl rs)
  | 0x74 => BPF_BINARY A32 BPF_RSH  rd (inr i)
  | 0x7c => BPF_BINARY A32 BPF_RSH  rd (inl rs)
  | 0x84 => BPF_NEG A32 rd
  | 0x94 => BPF_BINARY A32 BPF_MOD  rd (inr i)
  | 0x9c => BPF_BINARY A32 BPF_MOD  rd (inl rs)
  | 0xa4 => BPF_BINARY A32 BPF_XOR  rd (inr i)
  | 0xac => BPF_BINARY A32 BPF_XOR  rd (inl rs)
  | 0xb4 => BPF_BINARY A32 BPF_MOV  rd (inr i)
  | 0xbc => BPF_BINARY A32 BPF_MOV  rd (inl rs)
  | 0xc4 => BPF_BINARY A32 BPF_ARSH rd (inr i)
  | 0xcc => BPF_BINARY A32 BPF_ARSH rd (inl rs)

  | 0x18 => BPF_LDDW rd i
  | 0x61 => BPF_LDX Mint32         rd rs ofs
  | 0x69 => BPF_LDX Mint16unsigned rd rs ofs
  | 0x71 => BPF_LDX Mint8unsigned  rd rs ofs
  | 0x79 => BPF_LDX Mint64         rd rs ofs
  | 0x62 => BPF_ST  Mint32         rd (inr i)  ofs
  | 0x6a => BPF_ST  Mint16unsigned rd (inr i)  ofs
  | 0x72 => BPF_ST  Mint8unsigned  rd (inr i)  ofs
  | 0x7a => BPF_ST  Mint64         rd (inr i)  ofs
  | 0x63 => BPF_ST  Mint32         rd (inl rs) ofs
  | 0x6b => BPF_ST  Mint16unsigned rd (inl rs) ofs
  | 0x73 => BPF_ST  Mint8unsigned  rd (inl rs) ofs
  | 0x7b => BPF_ST  Mint64         rd (inl rs) ofs

  | 0x05 => BPF_JA ofs
  | 0x15 => BPF_JUMP  Eq           rd (inr i)  ofs
  | 0x1d => BPF_JUMP  Eq           rd (inl rs) ofs
  | 0x25 => BPF_JUMP (Gt Unsigned) rd (inr i)  ofs
  | 0x2d => BPF_JUMP (Gt Unsigned) rd (inl rs) ofs
  | 0x35 => BPF_JUMP (Ge Unsigned) rd (inr i)  ofs
  | 0x3d => BPF_JUMP (Ge Unsigned) rd (inl rs) ofs
  | 0xa5 => BPF_JUMP (Lt Unsigned) rd (inr i)  ofs
  | 0xad => BPF_JUMP (Lt Unsigned) rd (inl rs) ofs
  | 0xb5 => BPF_JUMP (Le Unsigned) rd (inr i)  ofs
  | 0xbd => BPF_JUMP (Le Unsigned) rd (inl rs) ofs
  | 0x45 => BPF_JUMP  SEt          rd (inr i)  ofs
  | 0x4d => BPF_JUMP  SEt          rd (inl rs) ofs
  | 0x55 => BPF_JUMP  Ne           rd (inr i)  ofs
  | 0x5d => BPF_JUMP  Ne           rd (inl rs) ofs
  | 0x65 => BPF_JUMP (Gt Signed)   rd (inr i)  ofs
  | 0x6d => BPF_JUMP (Gt Signed)   rd (inl rs) ofs
  | 0x75 => BPF_JUMP (Ge Signed)   rd (inr i)  ofs
  | 0x7d => BPF_JUMP (Ge Signed)   rd (inl rs) ofs
  | 0xc5 => BPF_JUMP (Lt Signed)   rd (inr i)  ofs
  | 0xcd => BPF_JUMP (Lt Signed)   rd (inl rs) ofs
  | 0xd5 => BPF_JUMP (Le Signed)   rd (inr i)  ofs
  | 0xdd => BPF_JUMP (Le Signed)   rd (inl rs) ofs

  | 0x95 => BPF_RET

  | _    => BPF_ERR
  end.
Close Scope nat_scope.

Definition decode (ins: int64): instruction :=
  let n_opcode := get_opcode ins in
  let n_dst    := int64_to_dst_reg ins in
  let n_src    := int64_to_src_reg ins in
  let n_ofs    := get_offset ins in
  let n_imm    := get_immediate ins in
     get_instruction n_opcode n_dst n_src n_ofs n_imm.
(*
Definition well_decode_imm (ins: int64) :=
  match decode ins with
  | BPF_BINARY _ _ _ rs | BPF_JUMP _ _ rs _ =>
    match rs with
    | inr i => exists vi, i = Vint vi
    | _ => True
    end
  | _ => True
  end.

Lemma get_immediate_vint:
  forall ins, get_immediate ins = Vint (Int.repr (Int64.unsigned (Int64.shru ins int64_32))).
Proof.
  unfold get_immediate; unfold val_intsoflongu, int64o_vlong.
  intros; reflexivity.
Qed.

Lemma decode_imm_vint:
  forall ins, well_decode_imm ins.
Proof.
  unfold well_decode_imm, decode.
  intros.
  destruct get_instruction eqn: H1; try (apply I).
  - destruct s; try (apply I).
    rewrite get_immediate_vint in H1.
    
Qed.*)
