From compcert Require Import Coqlib Integers AST Values Memory Ctypes Archi.
From Coq Require Import Lia ZArith.

Open Scope Z_scope.


Lemma Int64_max_unsigned_eq:
  Int64.max_unsigned = 18446744073709551615.
Proof.
  unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize; reflexivity.
Qed.

Lemma Int_max_unsigned_eq:
  Int.max_unsigned = 4294967295.
Proof.
  unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize; reflexivity.
Qed.

Lemma size_chunk_gt_zero:
  forall chunk, 0 < size_chunk chunk.
Proof.
  intros.
  unfold size_chunk.
  destruct chunk; try lia.
Qed.

Lemma size_chunk_int_range:
  forall chunk, 0 <= size_chunk chunk <= Int.max_unsigned.
Proof.
  unfold size_chunk; intros.
  rewrite Int_max_unsigned_eq.
  split; destruct chunk; try lia.
Qed.

(*
Lemma _32_lt_64:
  Int.ltu int32_32 Int64.iwordsize' = true.
Proof.
  unfold int32_32, Int64.iwordsize'.
  unfold Int64.zwordsize, Int64.wordsize, Wordsize_64.wordsize.
  unfold Int.ltu.
  simpl.
  assert (H0: 0 <= 32 <= Int.max_unsigned).
  unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize; simpl; lia.
  assert (H1: 0 <= 64 <= Int.max_unsigned).
  unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize; simpl; lia.
  rewrite Int.unsigned_repr; try assumption.
  rewrite Int.unsigned_repr; try assumption.
  simpl; reflexivity.
Qed.

Lemma sint16_to_int64_to_vlong:
  forall ofs,
    exists v, int64_to_vlong (sint16_to_int64 ofs) = Vlong v.
Proof.
  unfold int64_to_vlong, sint16_to_int64; intros.
  exists (Int64.repr (Int16.Int16.signed ofs)); reflexivity.
Qed. *)

Lemma Int64_unsigned_ge_0:
  forall v, 0 <= Int64.unsigned v.
Proof.
  intro v.
  assert (Hrange: 0 <= Int64.unsigned v <= Int64.max_unsigned). {
    apply Int64.unsigned_range_2.
  }
  destruct Hrange as [Ha Hb]; assumption.
Qed.

Lemma Int_repr_zero:
  forall v, 0<=v<=Int.max_unsigned -> Int.unsigned (Int.repr v) = Int.unsigned (Int.zero) -> v = 0.
Proof.
  intros.
  rewrite (Int.unsigned_repr v H) in H0.
  rewrite Int.unsigned_zero in H0.
  assumption.
Qed.

Lemma Ptrofs_of_int_unsigned:
  forall v, Ptrofs.unsigned (Ptrofs.of_int v) = Int.unsigned v.
Proof.
  intros.
  assert (H1: Ptrofs.agree32 (Ptrofs.of_int v) v). { apply Ptrofs.agree32_of_int. reflexivity. }
  rewrite H1; reflexivity.
Qed.

Lemma ptrofs_unsigned_ge_0:
  forall v, 0 <= Ptrofs.unsigned v.
Proof.
  intro v.
  assert (Hrange: 0 <= Ptrofs.unsigned v <= Ptrofs.max_unsigned). {
    apply Ptrofs.unsigned_range_2.
  }
  destruct Hrange as [Ha Hb]; assumption.
Qed.

Lemma Cle_implies_Zle:
  forall lo ofs,
    negb (Int64.ltu ofs lo) = true ->
      Int64.unsigned lo <= Int64.unsigned ofs.
Proof.
  intros.
  rewrite negb_true_iff in H.
  unfold Int64.ltu in H.
  destruct (zlt _ _) in H; try inversion H.
  lia.
Qed.

Lemma Clt_implies_Zlt:
  forall ofs hi,
    Int64.ltu ofs hi = true ->
      Int64.unsigned ofs < Int64.unsigned hi.
Proof.
  intros.
  unfold Int64.ltu in H.
  destruct (zlt _ _) in H; try inversion H.
  lia.
Qed.

Lemma unsigned_size_chunk_ge_0:
  forall ofs chunk,
    0 <= Int64.unsigned ofs + size_chunk chunk.
Proof.
  intros.
  assert (Hchunk_lo: 0 < size_chunk chunk). apply size_chunk_gt_zero.
  assert (Hofs_lo: 0<= Int64.unsigned ofs). apply Int64_unsigned_ge_0. 
  unfold size_chunk; destruct chunk; rewrite Z.add_comm; try lia.
Qed.

Lemma unsigned_ofs_size_chunk_ge_0:
  forall ofs chunk,
    Int64.unsigned ofs < Int64.unsigned ofs + size_chunk chunk.
Proof.
  intros.
  assert (Hchunk_lo: 0 < size_chunk chunk). apply size_chunk_gt_zero.
  assert (Hofs_lo: 0<= Int64.unsigned ofs). apply Int64_unsigned_ge_0. 
  lia.
Qed.

(**r Here is a problem, 'ofs+size_chunk':Z may be greater than Int64.mex_unsigned! 
     While the 'Vlong (Int64.repr (ofs+size_chunk))': Val is always within the range!
 *)
(*
Lemma hi_ofs_max_unsigned:
  forall ofs chunk,
    negb
         (Int64.ltu (Int64.repr (Int64.max_unsigned-(size_chunk chunk))) ofs) = true ->
      0 <= Int64.unsigned ofs + size_chunk chunk <= Int64.max_unsigned.
Proof.
  intros ofs chunk Hcmp.
  rewrite Int64_max_unsigned_eq in *.
  remember ((Int64.ltu (Int64.repr (18446744073709551615 - size_chunk chunk))) ofs) as k eqn: Hk.
  rewrite Hk in Hcmp; clear Hk.
  rewrite negb_true_iff in Hcmp.
  unfold Int64.ltu in Hcmp.
  destruct (zlt _ _) in Hcmp.
  - inversion Hcmp.
  - clear Hcmp.
    assert (Heq_max: 0 <= 18446744073709551615 - size_chunk chunk <= Int64.max_unsigned). {
      rewrite Int64_max_unsigned_eq.
      unfold size_chunk; destruct chunk; try lia.
    }
    rewrite (Int64.unsigned_repr _ Heq_max) in g.
    split.
    apply unsigned_size_chunk_ge_0.
    lia.
Qed.

Lemma Clt_implies_Zlt_add:
  forall ofs chunk hi, Int64.ltu (Int64.add ofs (Int64.repr (size_chunk chunk))) hi = true ->
    0 <= (Int64.unsigned ofs + size_chunk chunk) <= Int64.max_unsigned ->
      0<= Int64.unsigned ofs + (size_chunk chunk) < Int64.unsigned hi.
Proof.
  intros.
  split.
  apply unsigned_size_chunk_ge_0.
  unfold Int64.ltu, Int64.add in H.
  destruct (zlt _ _) in H; try inversion H.
  assert (H5: Int64.unsigned (Int64.repr (size_chunk chunk)) = size_chunk chunk). { apply Int64.unsigned_repr; apply size_chunk_int64_range; assumption. }
  rewrite H5 in l.
  assert (H6: Int64.unsigned (Int64.repr (Int64.unsigned ofs + size_chunk chunk)) = 
              (Int64.unsigned ofs + size_chunk chunk)). { apply Int64.unsigned_repr; assumption. }
  rewrite H6 in l; assumption.
Qed.
*)
Close Scope Z_scope.