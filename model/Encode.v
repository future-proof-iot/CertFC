From compcert Require Import Integers AST Ctypes.
From Coq Require Import ZArith.

From bpf.comm Require Import Flag Regs BinrBPF rBPFValues.
From bpf.model Require Import Syntax.

(** * Encode: from rBPF fields to int64 *)

(** @input
  * @v: value
  * @ins: the initial 64-bit binary instruction
  * @from: the starting location where save v

  * @output
  * a updated 64-bit binary instruction where from location `from` storing the value of `v`
  *)
Definition encode_bpf64 (v: int64) (ins: int64) (from: nat): int64 :=
  Int64.or (Int64.shl v (Int64.repr (Z.of_nat from))) ins.

(** o could be negative, so we only need low 16-bit *)
Definition bpf_ofs_to_int64 (ofs: int): int64 :=
  Int64.and (Int64.repr (Int.signed ofs)) (Int64.repr 0xffff).

Definition encode_bpf64_bop (src: reg+imm) (dst64: int64) (opi opr: Z): int64 :=
  match src with
  | inl r =>
    let src64 := Int64.repr (id_of_reg r) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr opr) 8 in
      encode_bpf64 src64 ins_dst 12
  | inr i =>
    let imm64 := Int64.repr (Int.signed i) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr opi) 8 in
      encode_bpf64 imm64 ins_dst 32
  end.

Definition encode_bpf64_cond_1 (src: reg+imm) (dst64 ofs64: int64) (opi opr: Z): int64 :=
  match src with
  | inl r =>
    let src64 := Int64.repr (id_of_reg r) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr opr) 8 in
    let ins_src := encode_bpf64 src64 ins_dst 12 in
      encode_bpf64 ofs64 ins_src 16
  | inr i =>
    let imm64 := Int64.repr (Int.signed i) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr opi) 8 in
    let ins_imm := encode_bpf64 imm64 ins_dst 32 in
      encode_bpf64 ofs64 ins_imm 16
  end.

Definition encode_bpf64_cond_2 (src: reg+imm) (dst64 ofs64: int64) (opiu opru opis oprs: Z) (s: signedness): int64 :=
  match src with
  | inl r =>
    let src64 := Int64.repr (id_of_reg r) in
    let ins_dst :=
      match s with
      | Unsigned  => encode_bpf64 dst64 (Int64.repr opru) 8
      | Signed    => encode_bpf64 dst64 (Int64.repr oprs) 8
      end in
    let ins_src := encode_bpf64 src64 ins_dst 12 in
      encode_bpf64 ofs64 ins_src 16
  | inr i =>
    let imm64 := Int64.repr (Int.signed i) in
    let ins_dst :=
      match s with
      | Unsigned  => encode_bpf64 dst64 (Int64.repr opiu) 8
      | Signed    => encode_bpf64 dst64 (Int64.repr opis) 8
      end in
    let ins_imm := encode_bpf64 imm64 ins_dst 32 in
      encode_bpf64 ofs64 ins_imm 16
  end.

Definition encode_bpf64_str (src: reg+imm) (dst64 ofs64: int64) (opi opr: Z): int64 :=
  match src with
  | inl r =>
    let src64 := Int64.repr (id_of_reg r) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr opr) 8 in
    let ins_src := encode_bpf64 src64 ins_dst 12 in
      encode_bpf64 ofs64 ins_src 16
  | inr i =>
    let imm64 := Int64.repr (Int.signed i) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr opi) 8 in
    let ins_imm := encode_bpf64 imm64 ins_dst 32 in
      encode_bpf64 ofs64 ins_imm 16
  end.

Definition bpf64_to_binary (ins: instruction): int64 :=
  match ins with
  | BPF_NEG a dst =>
    let dst64 := Int64.repr (id_of_reg dst) in
      match a with
      | A32 => encode_bpf64 dst64 (Int64.repr 0x84) 8
      | A64 => encode_bpf64 dst64 (Int64.repr 0x87) 8
      end
  | BPF_BINARY a bop dst src =>
    let dst64 := Int64.repr (id_of_reg dst) in
      match a with
      | A32 =>
        match bop with
        | BPF_ADD   => encode_bpf64_bop src dst64 0x04 0x0c
        | BPF_SUB   => encode_bpf64_bop src dst64 0x14 0x1c
        | BPF_MUL   => encode_bpf64_bop src dst64 0x24 0x2c
        | BPF_DIV   => encode_bpf64_bop src dst64 0x34 0x3c
        | BPF_OR    => encode_bpf64_bop src dst64 0x44 0x4c
        | BPF_AND   => encode_bpf64_bop src dst64 0x54 0x5c
        | BPF_LSH   => encode_bpf64_bop src dst64 0x64 0x6c
        | BPF_RSH   => encode_bpf64_bop src dst64 0x74 0x7c
        | BPF_MOD   => encode_bpf64_bop src dst64 0x94 0x9c
        | BPF_XOR   => encode_bpf64_bop src dst64 0xa4 0xac
        | BPF_MOV   => encode_bpf64_bop src dst64 0xb4 0xbc
        | BPF_ARSH  => encode_bpf64_bop src dst64 0xc4 0xcc
        end
      | A64 =>
        match bop with
        | BPF_ADD   => encode_bpf64_bop src dst64 0x07 0x0f
        | BPF_SUB   => encode_bpf64_bop src dst64 0x17 0x1f
        | BPF_MUL   => encode_bpf64_bop src dst64 0x27 0x2f
        | BPF_DIV   => encode_bpf64_bop src dst64 0x37 0x3f
        | BPF_OR    => encode_bpf64_bop src dst64 0x47 0x4f
        | BPF_AND   => encode_bpf64_bop src dst64 0x57 0x5f
        | BPF_LSH   => encode_bpf64_bop src dst64 0x67 0x6f
        | BPF_RSH   => encode_bpf64_bop src dst64 0x77 0x7f
        | BPF_MOD   => encode_bpf64_bop src dst64 0x97 0x9f
        | BPF_XOR   => encode_bpf64_bop src dst64 0xa7 0xaf
        | BPF_MOV   => encode_bpf64_bop src dst64 0xb7 0xbf
        | BPF_ARSH  => encode_bpf64_bop src dst64 0xc7 0xcf
        end
    end

  | BPF_JA o =>
    let ofs64 := bpf_ofs_to_int64 o in
      encode_bpf64 ofs64 (Int64.repr 0x05) 8

  | BPF_JUMP c dst src o =>
    let dst64 := Int64.repr (id_of_reg dst) in
    let ofs64 := bpf_ofs_to_int64 o in
      match c with
      | Eq    => encode_bpf64_cond_1 src dst64 ofs64 0x15 0x1d
      | SEt   => encode_bpf64_cond_1 src dst64 ofs64 0x55 0x5d
      | Ne    => encode_bpf64_cond_1 src dst64 ofs64 0x45 0x4d
      | Gt s  => encode_bpf64_cond_2 src dst64 ofs64 0x25 0x2d 0x65 0x6d s
      | Ge s  => encode_bpf64_cond_2 src dst64 ofs64 0x35 0x3d 0x75 0x7d s
      | Lt s  => encode_bpf64_cond_2 src dst64 ofs64 0xa5 0xad 0xc5 0xcd s
      | Le s  => encode_bpf64_cond_2 src dst64 ofs64 0xb5 0xbd 0xd5 0xdd s
      end

  | BPF_LDDW_low dst i =>
    let dst64 := Int64.repr (id_of_reg dst) in
    let imm64 := Int64.repr (Int.signed i) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr 0x18) 8 in
      encode_bpf64 imm64 ins_dst 32
  | BPF_LDDW_high dst i =>
    let dst64 := Int64.repr (id_of_reg dst) in
    let imm64 := Int64.repr (Int.signed i) in
    let ins_dst := encode_bpf64 dst64 (Int64.repr 0x10) 8 in
      encode_bpf64 imm64 ins_dst 32

  | BPF_LDX mc dst src o =>
    let dst64 := Int64.repr (id_of_reg dst) in
    let src64 := Int64.repr (id_of_reg src) in
    let ofs64 := bpf_ofs_to_int64 o in
      match mc with
      | Mint32          =>
        let ins_dst := encode_bpf64 dst64 (Int64.repr 0x61) 8 in
        let ins_src := encode_bpf64 src64 ins_dst 12 in
          encode_bpf64 ofs64 ins_src 16
      | Mint16unsigned  =>
        let ins_dst := encode_bpf64 dst64 (Int64.repr 0x69) 8 in
        let ins_src := encode_bpf64 src64 ins_dst 12 in
          encode_bpf64 ofs64 ins_src 16
      | Mint8unsigned   =>
        let ins_dst := encode_bpf64 dst64 (Int64.repr 0x71) 8 in
        let ins_src := encode_bpf64 src64 ins_dst 12 in
          encode_bpf64 ofs64 ins_src 16
      | Mint64          =>
        let ins_dst := encode_bpf64 dst64 (Int64.repr 0x79) 8 in
        let ins_src := encode_bpf64 src64 ins_dst 12 in
          encode_bpf64 ofs64 ins_src 16
      | _               => Int64.zero
      end

  | BPF_ST mc dst src o =>
    let dst64 := Int64.repr (id_of_reg dst) in
    let ofs64 := bpf_ofs_to_int64 o in
      match mc with
      | Mint32          => encode_bpf64_str src dst64 ofs64 0x62 0x63
      | Mint16unsigned  => encode_bpf64_str src dst64 ofs64 0x6a 0x6b
      | Mint8unsigned   => encode_bpf64_str src dst64 ofs64 0x72 0x73
      | Mint64          => encode_bpf64_str src dst64 ofs64 0x7a 0x7b
      | _               => Int64.zero
      end

  | BPF_CALL i =>
    let imm64 := Int64.repr (Int.signed i) in
      encode_bpf64 imm64 (Int64.repr 0x85) 16
  | BPF_RET => Int64.repr 0x95
  | BPF_ERR => Int64.zero
  end.