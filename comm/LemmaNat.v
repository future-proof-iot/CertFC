From compcert Require Import Zbits.
From Coq Require Import Lia ZArith.

(**r Implemented by FB
  a set of useful lemmas about Nat.land
 *)

Open Scope Z_scope.

Fixpoint Forall_exec (P : nat -> bool) (n: nat)  : bool :=
  match n with
  | O => P O
  | S n' => P n && Forall_exec P n'
  end.

Lemma Forall_exec_spec : forall P b,
    Forall_exec P b = true ->
    forall n, (n <= b)%nat -> P n = true.
Proof.
  induction b.
  - simpl. intros.
    assert (n=0%nat) by lia.
    subst. auto.
  - simpl. intros.
    rewrite Bool.andb_true_iff in H.
    assert ( n <= b \/ n = S b)%nat by lia.
    destruct H1 ; subst.
    apply IHb; auto. tauto.
    tauto.
Qed.

Lemma odd_of_nat : forall (n:nat), Z.odd (Z.of_nat n) = Nat.odd n.
Proof.
  intros.
  destruct (Nat.odd n) eqn:NO.
  - rewrite Nat.odd_spec in NO.
    unfold Nat.Odd in NO.
    destruct NO.
    subst.
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_mul.
    rewrite Z.add_comm.
    rewrite Z.odd_add_mul_2.
    reflexivity.
  - destruct (Z.odd (Z.of_nat n)) eqn:ZO; auto.
    rewrite Z.odd_spec in ZO.
    destruct ZO.
    assert (exists m, n = 1 + 2 * m)%nat.
    exists (Z.to_nat x). lia.
    destruct H0.
    subst.
    rewrite Nat.odd_add_mul_2 in NO.
    discriminate.
Qed.

Lemma testbit_of_nat : forall m n,
  Z.testbit (Z.of_nat n) (Z.of_nat m) = Nat.testbit n m.
Proof.
  induction m.
  - intros.
    simpl. apply odd_of_nat.
  - rewrite Nat2Z.inj_succ.
    simpl. intro.
    rewrite <- IHm.
    rewrite Ztestbit_succ by lia.
    f_equal.
    rewrite Nat.div2_div.
    rewrite div_Zdiv by lia.
    lia.
Qed.

Lemma testbit_of_nat_ext : forall i n,
    Z.testbit (Z.of_nat n) i = if Z.leb 0 i
                               then Nat.testbit n (Z.to_nat i)
                               else false.
Proof.
  intros.
  destruct (0 <=? i) eqn:LE.
  -
    apply Zle_bool_imp_le  in LE.
    assert (exists m, Z.of_nat m = i).
    {
      exists (Z.to_nat i).
      lia.
    }
    destruct H as (m & EQ).
    rewrite <- EQ.
    assert (Z.to_nat (Z.of_nat m) = m) by lia.
    rewrite H.
    apply testbit_of_nat.
  - assert (i < 0) by lia.
    destruct i.
    + lia.
    + lia.
    + reflexivity.
Qed.

Lemma land_land : forall n m,
    Z.land (Z.of_nat n) (Z.of_nat m) = Z.of_nat (Nat.land n m).
Proof.
  intros.
  apply Z.bits_inj.
  unfold Z.eqf.
  intros.
  rewrite testbit_of_nat_ext.
  destruct (0 <=? n0) eqn:NO.
  assert (exists i, n0 = Z.of_nat i).
  {
    exists (Z.to_nat n0).
    lia.
  }
  destruct H. subst.
  assert (Z.to_nat (Z.of_nat x) = x) by lia.
  rewrite  H.
  rewrite Z.land_spec.
  rewrite Nat.land_spec.
  rewrite !testbit_of_nat. (**r ? (without natural) performs the rewrite as many times as possible (possibly zero times). This form never fails. ! (without natural) performs the rewrite as many times as possible and at least once. The tactic fails if the requested number of rewrites can't be performed. *)
  reflexivity.
  rewrite Z.land_spec.
  rewrite! testbit_of_nat_ext.
  destruct(0 <=? n0) ; try congruence.
  reflexivity.
Qed.

Close Scope Z_scope.

Lemma land_bound : forall n x, Nat.land n x <= n.
Proof.
  unfold Nat.land.
  intros n x.
  assert (forall n a b, a <= n -> Nat.bitwise andb n a b <= a).
  {
    clear.
    induction n.
    - simpl. lia.
    - intros.
      simpl.
      assert (Nat.bitwise andb n (Nat.div2 a) (Nat.div2 b) <= (Nat.div2 a)).
      {
        apply IHn.
        apply Nat.div2_decr.
        auto.
      }
      revert H0.
      generalize (Nat.bitwise andb n (Nat.div2 a) (Nat.div2 b)) as n1.
      intros.
      rewrite Nat.div2_div in H0.
      rewrite (Nat.div_mod a 2) at 2 by lia.
      assert (a mod 2 = if Nat.odd a then 1 else 0).
      {
        destruct (Nat.odd a) eqn:O.
        apply Nat.odd_spec in O.
        unfold Nat.Odd in O.
        destruct O as (m & E).
        subst.
        replace (2 * m + 1) with (1 + m * 2) by lia.
        rewrite Nat.mod_add. reflexivity.
        lia.
        assert (negb (Nat.odd a) = true).
        { rewrite O; reflexivity. }
        rewrite Nat.negb_odd in H1.
        rewrite Nat.even_spec in H1.
        destruct H1 as (x & EQ).
        subst.
        rewrite mult_comm.
        rewrite Nat.mod_mul. reflexivity. lia.
      }
      destruct  (Nat.odd a).
      rewrite H1.
      unfold andb.
      destruct (Nat.odd b) ; lia.
      unfold andb. lia.
  }
  apply H.
  lia.
Qed.