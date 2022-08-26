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

From Coq Require Import List ZArith Lia.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert Require Import Integers Values Memtype Memory.

Open Scope Z_scope.

(** permission_eq_eq: permission_eq -> permission_eq -> bool
  *)

Definition perm_ge (x y: permission): bool := if (Mem.perm_order_dec x y) then true else false.

(** * Some extra  CompCert Coqlib lemmas *)

Lemma proj_sumbool_false:
  forall (P Q: Prop) (a: {P}+{Q}), Coqlib.proj_sumbool a = false -> Q.
Proof.
  intros.
  destruct a; simpl.
  simpl in *.
  inversion H.
  auto.
Qed.

Lemma proj_sumbool_is_false:
  forall (P Q: Prop) (a: {P}+{~P}), ~P -> Coqlib.proj_sumbool a = false.
Proof.
  intros.
  unfold Coqlib.proj_sumbool.
  destruct a; simpl.
  congruence.
  auto.
Qed.


(** * Some extra CompCert Memory lemmas *)

Lemma store_perm_iff:
  forall chunk m1 m2 b ofs addr b0 ofs0 k p
  (Hstore : Mem.store chunk m1 b ofs addr = Some m2),
      Mem.perm m1 b0 ofs0 k p <-> Mem.perm m2 b0 ofs0 k p.
Proof.
  intros.
  split; intro.
  - eapply Mem.perm_store_1 with (k:=k) (p:=p) in Hstore; eauto.
  - eapply Mem.perm_store_2 with (k:=k) (p:=p) in Hstore; eauto.
Qed.

(**r the proof code comes from MisakaCenter (QQ), thx *)
Lemma mem_get_in:
  forall l (n:nat) q c,
  lt n (List.length l) ->
    Maps.ZMap.get (q + (Z.of_nat n)) (Mem.setN l q c) = (nth_default Memdata.Undef l n).
Proof.
  induction l; simpl in *; intros.
  lia.
  induction n; simpl.
  - unfold nth_default; simpl.
    rewrite Mem.setN_outside; try lia.
    rewrite Z.add_0_r.
    rewrite Maps.ZMap.gss; auto.
  - assert (Heq: nth_default Memdata.Undef (a::l) (S n) = nth_default Memdata.Undef l n) by auto.
    rewrite Heq; clear Heq.
    rewrite <- IHl with (q := q+1) (c:=Maps.ZMap.set q a c).
    assert (Heq: q + Z.pos (Pos.of_succ_nat n) = q + 1 + Z.of_nat n) by lia.
    rewrite Heq; clear Heq.
    reflexivity.
    lia.
Qed.

Lemma store_range_perm:
  forall chunk m1 m2 b0 b1 ofs addr low high k p
    (Hblk_neq: b0 <> b1)
    (Hstore : Mem.store chunk m1 b0 ofs addr = Some m2)
    (Hrange_perm : Mem.range_perm m1 b1 low high k p),
      Mem.range_perm m2 b1 low high k p.
Proof.
  intros.
  unfold Mem.range_perm in *.
  intros.
  specialize (Hrange_perm ofs0 H).
  eapply Mem.perm_store_1; eauto.
Qed.

Lemma store_valid_access_None:
  forall chunk m b ofs v,
  Mem.store chunk m b ofs v = None <-> ~ Mem.valid_access m chunk b ofs Writable.
Proof.
  intros.
  Global Transparent Mem.store.
  unfold Mem.store.
  destruct Mem.valid_access_dec eqn: Hdec.
  intuition.
  inversion H.

  intuition.
Qed.

Lemma unchanged_on_store_None:
  forall P m0 m1 chunk b ofs v
    (Hunchanged_on : Mem.unchanged_on P m0 m1)
    (Hvalid_block_implies : Mem.valid_block m1 b -> Mem.valid_block m0 b)
    (Hprop: forall i, ofs <= i < ofs + size_chunk chunk -> P b i),
      Mem.store chunk m0 b ofs v = None <-> Mem.store chunk m1 b ofs v = None.
Proof.
  intros.
  repeat rewrite store_valid_access_None.

  split; intros Hinvalid HF; apply Hinvalid; clear Hinvalid;
    unfold Mem.valid_access in *; destruct HF as (Hrange & HF).
  - split; [clear HF | assumption].
    unfold Mem.range_perm in *.
    intros.
    specialize (Hrange ofs0 H).
    eapply Mem.perm_unchanged_on_2; eauto.
    apply Hvalid_block_implies.
    eapply Mem.perm_valid_block; eauto.
  - split; [clear HF | assumption].
    unfold Mem.range_perm in *.
    intros.
    specialize (Hrange ofs0 H).
    eapply Mem.perm_unchanged_on; eauto.
Qed.

Lemma unchanged_on_valid_pointer:
  forall P m0 m1 b ofs
    (Hunchanged_on : Mem.unchanged_on P m0 m1)
    (Hvalid: Mem.valid_block m0 b)
    (Hprop: forall i, ofs <= i < ofs + 1 -> P b i),
    Mem.valid_pointer m0 b ofs =
    Mem.valid_pointer m1 b ofs.
Proof.
  intros.
  destruct Mem.valid_pointer eqn: Hvptr.
  - symmetry.
    rewrite Mem.valid_pointer_valid_access in *.
    unfold Mem.valid_access in *.
    intuition.
    clear H0.
    unfold Mem.range_perm in *.
    intros.
    specialize (H ofs0 H0).
    eapply Mem.perm_unchanged_on; eauto.
  - symmetry.
    rewrite <- Bool.not_true_iff_false in *.
    intro Hf.
    apply Hvptr.
    rewrite Mem.valid_pointer_valid_access in *.
    unfold Mem.valid_access in *.
    intuition.
    clear H0 H1.
    unfold Mem.range_perm in *.
    intros.
    specialize (H ofs0 H0).
    eapply Mem.perm_unchanged_on_2; eauto.
Qed.
