From compcert Require Import Integers AST Ctypes.
From Coq Require Import ZArith Ascii String HexString List.

From bpf.comm Require Import Flag Regs BinrBPF rBPFValues ListAsArray.
From bpf.model Require Import Syntax.

Import ListNotations.

(** * rBPF Print Module *)

(** This file is used to print rBPF instructions from syntax *)

Definition string_of_reg (r: reg): string :=
  match r with
  | R0 => "R0"
  | R1 => "R1"
  | R2 => "R2"
  | R3 => "R3"
  | R4 => "R4"
  | R5 => "R5"
  | R6 => "R6"
  | R7 => "R7"
  | R8 => "R8"
  | R9 => "R9"
  | R10 => "R10"
  end.

(* TODO: nat_to_string

Definition nat_to_string_aux (n: nat): string :=
  if Nat.eqb n 0 then "0"
  else if Nat.eqb n 1 then "1"
  else if Nat.eqb n 2 then "2"
  else if Nat.eqb n 3 then "3"
  else if Nat.eqb n 4 then "4"
  else if Nat.eqb n 5 then "5"
  else if Nat.eqb n 6 then "6"
  else if Nat.eqb n 7 then "7"
  else if Nat.eqb n 8 then "8"
  else "9".

Compute (of_nat 0x66).
Fixpoint string_of_nat (n: nat): string :=
  match n with
  | O => ""
  | S m =>
    let k := Nat.modulo n 10 in
    let l := Nat.div n 10 in
      (string_of_nat l) ++ (nat_to_string_aux k)
  end. *)

Definition string_of_int_unsigned (i: int): string := of_Z (Int.unsigned i).

Definition string_of_int_signed (i: int): string := of_Z (Int.signed i).

Definition print_reg_imm (ri: reg+imm): string :=
  match ri with
  | inl r => string_of_reg r
  | inr i => string_of_int_signed i
  end.

Definition string_of_signedness (s: signedness): string :=
  match s with
  | Signed => "(signed)"
  | Unsigned => ""
  end.

Definition string_of_memory_chunk (mc: memory_chunk): string :=
  match mc with
  | Mint32          => "32"
  | Mint16unsigned  => "16"
  | Mint8unsigned   => "8"
  | Mint64          => "64"
  | _               => "error"
  end.

Definition print_rBPF_instruction (ins: instruction): string :=
  match ins with
  | BPF_NEG a dst =>
    let dst_string := string_of_reg dst in
      dst_string ++ "= -" ++ dst_string
  | BPF_BINARY a bop dst src =>
    let dst_string := string_of_reg dst in
    let src_string := print_reg_imm src in
      match bop with
      | BPF_ADD   => dst_string ++ " += " ++ src_string
      | BPF_SUB   => dst_string ++ " -= " ++ src_string
      | BPF_MUL   => dst_string ++ " *= " ++ src_string
      | BPF_DIV   => dst_string ++ " /= " ++ src_string
      | BPF_OR    => dst_string ++ " |= " ++ src_string
      | BPF_AND   => dst_string ++ " &= " ++ src_string
      | BPF_LSH   => dst_string ++ " <<= " ++ src_string
      | BPF_RSH   => dst_string ++ " >>= " ++ src_string
      | BPF_MOD   => dst_string ++ " %= " ++ src_string
      | BPF_XOR   => dst_string ++ " ^= " ++ src_string
      | BPF_MOV   => dst_string ++ " = " ++ src_string
      | BPF_ARSH  => dst_string ++ " >>= (signed)" ++ src_string
      end

  | BPF_JA o =>
    let ofs_string := string_of_int_signed o in
      "goto " ++ ofs_string

  | BPF_JUMP c dst src o =>
    let dst_string := string_of_reg dst in
    let src_string := print_reg_imm src in
    let ofs_string := string_of_int_signed o in
      match c with
      | Eq    => "if " ++ dst_string ++ " == " ++ src_string ++ " goto " ++ ofs_string
      | SEt   => "if " ++ dst_string ++ " & " ++ src_string ++ " goto " ++ ofs_string
      | Ne    => "if " ++ dst_string ++ " != " ++ src_string ++ " goto " ++ ofs_string
      | Gt s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " > "  ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      | Ge s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " >= " ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      | Lt s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " < "  ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      | Le s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " <= " ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      end

  | BPF_LDDW_low dst i =>
    let dst_string := string_of_reg dst in
    let imm_string := string_of_int_unsigned i in
      dst_string ++ " = " ++ imm_string ++ " (lddw)"
  | BPF_LDDW_high dst i =>
    let dst_string := string_of_reg dst in
    let imm_string := string_of_int_unsigned i in
      dst_string ++ " |= (" ++ imm_string ++ " << 32)"

  | BPF_LDX mc dst src o =>
    let dst_string := string_of_reg dst in
    let src_string := string_of_reg src in
    let ofs_string := string_of_int_signed o in
      dst_string ++ " = *(u" ++ (string_of_memory_chunk mc) ++ " *)(" ++
        src_string ++ " + " ++ ofs_string ++ ")"

  | BPF_ST mc dst src o =>
    let dst_string := string_of_reg dst in
    let src_string := print_reg_imm src in
    let ofs_string := string_of_int_signed o in
      "*(u" ++ (string_of_memory_chunk mc) ++ " *)(" ++ dst_string ++ " + " ++ ofs_string ++ ") = " ++ src_string

  | BPF_CALL i => "call " ++ (string_of_int_signed i)
  | BPF_RET => "exit"
  | BPF_ERR => "error"
  end.

Fixpoint print_rBPF_prog_aux (pc: nat) (l: list instruction): list string :=
  match l with
  | [] => []
  | hd :: tl =>
    let ins_string := print_rBPF_instruction hd in
      List.app [((of_nat pc) ++ ": " ++ ins_string)%string] (print_rBPF_prog_aux (S pc) tl)
  end.

Definition print_rBPF_prog (l: list instruction): list string :=
  print_rBPF_prog_aux 0 l.

