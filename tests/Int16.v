From Coq Require Import ZArith.
From compcert Require Import Coqlib Integers.

Module Wordsize_16.
  Definition wordsize := 16%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
Proof.
unfold wordsize; congruence. Qed.
End Wordsize_16.

Strategy opaque [Wordsize_16.wordsize].

Module Int16 := Make(Wordsize_16).

Strategy 0 [Wordsize_16.wordsize].

Notation int16 := Int16.int.

Definition uint64_to_int (i:int64) := Int.repr (Int64.unsigned i).
Definition sint64_to_int (i:int64) := Int.repr (Int64.signed i).
Definition uint_to_int64 (i:int) := Int64.repr (Int.unsigned i).
Definition sint_to_int64 (i:int) := Int64.repr (Int.signed i).
Definition uint_to_int (i:int) := Int.repr (Int.unsigned i).
Definition sint_to_int (i:int) := Int.repr (Int.signed i).

Definition s64_add_us (x y: int64) : int64 :=
  Int64.repr (Int64.unsigned x + Int64.signed y).
Definition s64_sub_us (x y: int64) : int64 :=
  Int64.repr (Int64.unsigned x - Int64.signed y).
Definition s64_mul_us (x y: int64) : int64 :=
  Int64.repr (Int64.unsigned x * Int64.signed y).
Definition s64_divu_us (x y: int64) : int64 :=
  Int64.repr (Int64.unsigned x / Int64.signed y).
Definition s64_modu_us (x y: int64) : int64 :=
  Int64.repr ((Int64.unsigned x) mod (Int64.signed y)).

Definition s64_and_us (x y: int64): int64 := Int64.repr (Z.land (Int64.unsigned x) (Int64.signed y)).
Definition s64_or_us (x y: int64): int64 := Int64.repr (Z.lor (Int64.unsigned x) (Int64.signed y)).
Definition s64_xor_us (x y: int64) : int64 := Int64.repr (Z.lxor (Int64.unsigned x) (Int64.signed y)).

Definition s64_shl_us (x y: int64): int64 := Int64.repr (Z.shiftl (Int64.unsigned x) (Int64.signed y)).
Definition s64_shru_us (x y: int64): int64 := Int64.repr (Z.shiftr (Int64.unsigned x) (Int64.signed y)).
Definition s64_shr_us (x y: int64): int64 := Int64.repr (Z.shiftr (Int64.signed x) (Int64.signed y)).

Definition s32_add_us (x y: int) : int :=
  Int.repr (Int.unsigned x + Int.signed y).
Definition s32_sub_us (x y: int) : int :=
  Int.repr (Int.unsigned x - Int.signed y).
Definition s32_mul_us (x y: int) : int :=
  Int.repr (Int.unsigned x * Int.signed y).
Definition s32_divu_us (x y: int) : int :=
  Int.repr (Int.unsigned x / Int.signed y).
Definition s32_modu_us (x y: int) : int :=
  Int.repr ((Int.unsigned x) mod (Int.signed y)).

Definition s32_and_us (x y: int): int := Int.repr (Z.land (Int.unsigned x) (Int.signed y)).
Definition s32_or_us (x y: int): int := Int.repr (Z.lor (Int.unsigned x) (Int.signed y)).
Definition s32_xor_us (x y: int) : int := Int.repr (Z.lxor (Int.unsigned x) (Int.signed y)).

Definition s32_shl_us (x y: int): int := Int.repr (Z.shiftl (Int.unsigned x) (Int.signed y)).
Definition s32_shru_us (x y: int): int := Int.repr (Z.shiftr (Int.unsigned x) (Int.signed y)).
Definition s32_shr_us (x y: int): int := Int.repr (Z.shiftr (Int.signed x) (Int.signed y)).

Definition s32_eq_us (x y: int) : bool :=
  if zeq (Int.unsigned x) (Int.signed y) then true else false.
Definition s32_lt_us (x y: int) : bool :=
  if zlt (Int.unsigned x) (Int.signed y) then true else false.
Definition s32_lt_su (x y: int) : bool :=
  if zlt (Int.signed x) (Int.unsigned y) then true else false.

Definition s32_cmp_us (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => s32_eq_us x y
  | Cne => negb (s32_eq_us x y)
  | Clt => s32_lt_us x y
  | Cle => negb (s32_lt_su y x)
  | Cgt => s32_lt_su y x
  | Cge => negb (s32_lt_us x y)
  end.

Definition s64_eq_us (x y: int64) : bool :=
  if zeq (Int64.unsigned x) (Int64.signed y) then true else false.
Definition s64_lt_us (x y: int64) : bool :=
  if zlt (Int64.unsigned x) (Int64.signed y) then true else false.
Definition s64_lt_su (x y: int64) : bool :=
  if zlt (Int64.signed x) (Int64.unsigned y) then true else false.

Definition s64_cmp_us (c: comparison) (x y: int64) : bool :=
  match c with
  | Ceq => s64_eq_us x y
  | Cne => negb (s64_eq_us x y)
  | Clt => s64_lt_us x y
  | Cle => negb (s64_lt_su y x)
  | Cgt => s64_lt_su y x
  | Cge => negb (s64_lt_us x y)
  end.