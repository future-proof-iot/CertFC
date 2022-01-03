From bpf.src Require Import DxIntegers DxValues DxAST DxRegs DxFlag.
From compcert Require Import Integers.
From Coq Require Import ZArith.
Open Scope Z_scope.

(** common libs for clightlogic

*)

Definition id_of_reg (r:reg) : Z :=
  match r with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  | R8 => 8
  | R9 => 9
  | R10 => 10
  end.

Definition Z_of_flag (f:bpf_flag) : Z :=
  match f with
  | BPF_SUCC_RETURN  => 1
  | BPF_OK  => 0
  | BPF_ILLEGAL_INSTRUCTION => -1
  | BPF_ILLEGAL_MEM => -2
  | BPF_ILLEGAL_JUMP => -3
  | BPF_ILLEGAL_CALL => -4
  | BPF_ILLEGAL_LEN  => -5
  | BPF_ILLEGAL_REGISTER => -6
  | BPF_NO_RETURN => -7
  | BPF_OUT_OF_BRANCHES => -8
  | BPF_ILLEGAL_DIV => -9
  | BPF_ILLEGAL_SHIFT => -10
  | BPF_ILLEGAL_ALU => -11
  | BPF_UNDEF_ERROR => -12
  end.

Definition int_of_flag (f:bpf_flag)  :=
  Int.repr (Z_of_flag f).


Close Scope Z_scope.