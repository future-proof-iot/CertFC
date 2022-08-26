(**************************************************************************)
(*  This file is part of CertrBPF,                                        *)
(*  a formally verified rBPF verifier + interpreter + JIT in Coq.         *)
(*                                                                        *)
(*  Copyright (C) 2022 Inria                                              *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(*                                                                        *)
(**************************************************************************)

From compcert Require Import Coqlib Integers.
From Coq Require Import Lia ZArith.

Open Scope Z_scope.
(** Integer.max_unsigned *)

Global Transparent Int.repr.
Global Transparent Archi.ptr64.

Lemma Int_max_unsigned_eq64:
  Int.max_unsigned = 4294967295%Z.
Proof.
  unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize.
  reflexivity.
Qed.

Lemma Ptrofs_max_unsigned_eq32:
  Ptrofs.max_unsigned = 4294967295.
Proof.
  unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  reflexivity.
Qed.

Lemma Int_unsigned_ge_zero :
  forall i,
    Int.unsigned i >= 0.
Proof.
  intro.
  assert (Hrange: 0 <= Int.unsigned i <= Int.max_unsigned). { apply Int.unsigned_range_2. }
  destruct Hrange.
  (**r Search (_ <= _). *)
  apply Z.le_ge in H.
  assumption.
Qed.

Lemma Ptrofs_unsigned_ge_zero :
  forall i,
    Ptrofs.unsigned i >= 0.
Proof.
  intro.
  assert (Hrange: 0 <= Ptrofs.unsigned i <= Ptrofs.max_unsigned). { apply Ptrofs.unsigned_range_2. }
  destruct Hrange.
  (**r Search (_ <= _). *)
  apply Z.le_ge in H.
  assumption.
Qed.

Lemma Ptrofs_unsigned_repr_n:
  forall n,
  0 <= n <= 4294967295 ->
  Ptrofs.unsigned (Ptrofs.repr n) = n.
Proof.
  intros.
  rewrite Ptrofs.unsigned_repr; [reflexivity | rewrite Ptrofs_max_unsigned_eq32; lia].
Qed.

Lemma Int_unsigned_repr_n:
  forall n,
  0 <= n <= 4294967295 ->
  Int.unsigned (Int.repr n) = n.
Proof.
  intros.
  rewrite Int.unsigned_repr; [reflexivity | rewrite Int_max_unsigned_eq64; lia].
Qed.

Lemma Hint_unsigned_int64:
    forall i, (Int64.unsigned (Int64.repr (Int.unsigned i))) = (Int.unsigned i).
Proof.
    intro.
    rewrite Int64.unsigned_repr; [reflexivity |].
    assert (Hrange: 0 <= Int.unsigned i <= Int.max_unsigned). { apply Int.unsigned_range_2. }
    change Int.max_unsigned with 4294967295 in Hrange.
    change Int64.max_unsigned with 18446744073709551615.
    lia.
Qed.

Lemma Hzeq_neq_intro:
    forall (A:Type) a n (b c: A),
      (a <> n)%nat -> (if Coqlib.zeq (Z.of_nat n) (Z.of_nat a) then b else c) = c.
Proof.
  intros.
  apply zeq_false.
  intro.
  apply Nat2Z.inj in H0.
  lia.
Qed.

Lemma Int_repr_eq:
  forall a b
    (Ha_range: 0 <= a <= Int.max_unsigned)
    (Hb_range: 0 <= b <= Int.max_unsigned)
    (Heq: Int.repr a = Int.repr b),
      a = b.
Proof.
  intros.
  unfold Int.repr in Heq.
  inversion Heq.
  do 2 rewrite Int.Z_mod_modulus_eq in H0.
  change Int.modulus with 4294967296 in H0.
  change Int.max_unsigned with 4294967295 in *.
  rewrite Z.mod_small in H0; [ | lia].
  rewrite Z.mod_small in H0; [ | lia].
  assumption.
Qed.

Lemma Clt_Zlt_signed:
  forall ofs hi,
    Int.lt ofs hi = true ->
      Int.signed ofs < Int.signed hi.
Proof.
  intros.
  unfold Int.lt in H.
  destruct (Coqlib.zlt _ _) in H; try inversion H.
  assumption.
Qed.

Lemma Cle_Zle_signed:
  forall lo ofs,
    negb (Int.lt ofs lo) = true ->
      Int.signed lo <= Int.signed ofs.
Proof.
  intros.
  rewrite negb_true_iff in H.
  unfold Int.lt in H.
  destruct (Coqlib.zlt _ _) in H; try inversion H.
  lia.
Qed.

Lemma Clt_Zlt_unsigned:
  forall ofs hi,
    Int.ltu ofs hi = true ->
      Int.unsigned ofs < Int.unsigned hi.
Proof.
  intros.
  unfold Int.ltu in H.
  destruct (Coqlib.zlt _ _) in H; try inversion H.
  assumption.
Qed.

Lemma Cle_Zle_unsigned:
  forall lo ofs,
    negb (Int.ltu ofs lo) = true ->
      Int.unsigned lo <= Int.unsigned ofs.
Proof.
  intros.
  rewrite negb_true_iff in H.
  unfold Int.ltu in H.
  destruct (Coqlib.zlt _ _) in H; try inversion H.
  lia.
Qed.


Close Scope Z_scope.