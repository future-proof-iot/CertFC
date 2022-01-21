From compcert Require Import Integers.
From bpf.src Require Import DxOpcode.
From Coq Require Import Lia ZArith.

Open Scope Z_scope.

Lemma nat8_land_240_255_eq:
  forall (n:nat)
    (Hnat8: (n <= 255)%nat),
    (Int.and (Int.and (Int.repr (Z.of_nat n)) (Int.repr 240)) (Int.repr 255)) = Int.repr (Z.of_nat (Nat.land n 240)).
Proof.
  intros.
  do 255 (destruct n; [reflexivity | apply le_S_n in Hnat8]).
  destruct n; [reflexivity | idtac].
  exfalso; apply Nat.nle_succ_0 in Hnat8; assumption.
Qed.

Open Scope nat_scope.
Definition byte_to_opcode_alu64_if (op: nat): opcode_alu64 :=
  let opcode_alu := Nat.land op 0xf0 in (**r masking operation *)
    if opcode_alu =? 0x00 then op_BPF_ADD64
    else if opcode_alu =? 0x10 then op_BPF_SUB64
    else if opcode_alu =? 0x20 then op_BPF_MUL64
    else if opcode_alu =? 0x30 then op_BPF_DIV64
    else if opcode_alu =? 0x40 then op_BPF_OR64
    else if opcode_alu =? 0x50 then op_BPF_AND64
    else if opcode_alu =? 0x60 then op_BPF_LSH64
    else if opcode_alu =? 0x70 then op_BPF_RSH64
    else if opcode_alu =? 0x80 then if Nat.eqb op 0x87 then op_BPF_NEG64 else op_BPF_ALU64_ILLEGAL_INS
    else if opcode_alu =? 0x90 then op_BPF_MOD64
    else if opcode_alu =? 0xa0 then op_BPF_XOR64
    else if opcode_alu =? 0xb0 then op_BPF_MOV64
    else if opcode_alu =? 0xc0 then op_BPF_ARSH64
    else op_BPF_ALU64_ILLEGAL_INS
  .

Lemma byte_to_opcode_alu64_if_same:
  forall (op: nat),
    byte_to_opcode_alu64 op = byte_to_opcode_alu64_if op.
Proof.
  intros.
  unfold byte_to_opcode_alu64, byte_to_opcode_alu64_if.
  generalize (Nat.land op 240); intro.
  do 192 (destruct n; [reflexivity | idtac]).
  destruct n; [reflexivity | reflexivity].
Qed.


Ltac simpl_nat :=
  match goal with
  | H: ?X <> ?Y |- context [if (?X =? ?Y) then _ else _] =>
    destruct (X =? Y) eqn: Ht; [rewrite Nat.eqb_eq in Ht; intuition | try reflexivity]; clear Ht
  end.

Lemma byte_to_opcode_alu64_if_default:
  forall op
    (Hadd: Nat.land op 240 <> 0x00)
    (Hsub: Nat.land op 240 <> 0x10)
    (Hmul: Nat.land op 240 <> 0x20)
    (Hdiv: Nat.land op 240 <> 0x30)
    (Hor:  Nat.land op 240 <> 0x40)
    (Hand: Nat.land op 240 <> 0x50)
    (Hlsh: Nat.land op 240 <> 0x60)
    (Hrsh: Nat.land op 240 <> 0x70)
    (Hneg: Nat.land op 240 <> 0x80)
    (Hmod: Nat.land op 240 <> 0x90)
    (Hxor: Nat.land op 240 <> 0xa0)
    (Hmov: Nat.land op 240 <> 0xb0)
    (Harsh: Nat.land op 240 <> 0xc0),
      byte_to_opcode_alu64_if op = op_BPF_ALU64_ILLEGAL_INS.
Proof.
  intros.
  unfold byte_to_opcode_alu64_if.
  repeat simpl_nat.
Qed.

Definition byte_to_opcode_branch_if (op: nat): opcode_branch :=
  let opcode_alu := Nat.land op 0xf0 in (**r masking operation *)
    if opcode_alu =? 0x00 then if Nat.eqb op 0x05 then op_BPF_JA else op_BPF_JMP_ILLEGAL_INS
    else if opcode_alu =? 0x10 then op_BPF_JEQ
    else if opcode_alu =? 0x20 then op_BPF_JGT
    else if opcode_alu =? 0x30 then op_BPF_JGE
    else if opcode_alu =? 0xa0 then op_BPF_JLT
    else if opcode_alu =? 0xb0 then op_BPF_JLE
    else if opcode_alu =? 0x40 then op_BPF_JSET
    else if opcode_alu =? 0x50 then op_BPF_JNE
    else if opcode_alu =? 0x60 then op_BPF_JSGT
    else if opcode_alu =? 0x70 then op_BPF_JSGE
    else if opcode_alu =? 0xc0 then op_BPF_JSLT
    else if opcode_alu =? 0xd0 then op_BPF_JSLE
    else if opcode_alu =? 0x90 then if Nat.eqb op 0x95 then op_BPF_RET else op_BPF_JMP_ILLEGAL_INS
    else op_BPF_JMP_ILLEGAL_INS
  .

Lemma byte_to_opcode_branch_if_same:
  forall (op: nat),
    byte_to_opcode_branch op = byte_to_opcode_branch_if op.
Proof.
  intros.
  unfold byte_to_opcode_branch, byte_to_opcode_branch_if.
  generalize (Nat.land op 240); intro.
  do 192 (destruct n; [reflexivity | idtac]).
  do 16 (destruct n; [reflexivity | idtac]).
  destruct n; [reflexivity | reflexivity].
Qed.

Lemma nat8_neq_135:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 135),
      Int.repr (Z.of_nat n) <> Int.repr 135.
Proof.
  intros.
  Transparent Int.repr.
  do 100 (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  do 35 (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  apply Hc2_eq; reflexivity.
  do 119 (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | ]).
  exfalso; apply Nat.nle_succ_0 in Hrange; assumption.
Qed.

Lemma nat8_neq_5:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 5),
      Int.repr (Z.of_nat n) <> Int.repr 5.
Proof.
  intros.
  Transparent Int.repr.
  do 5 (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  apply Hc2_eq; reflexivity.
  do 249 (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | ]).
  exfalso; apply Nat.nle_succ_0 in Hrange; assumption.
Qed.


Lemma nat8_neq_149:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 149),
      Int.repr (Z.of_nat n) <> Int.repr 149.
Proof.
  intros.
  Transparent Int.repr.
  do 150 (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  apply Hc2_eq; reflexivity.
  do 105 (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | apply le_S_n in Hrange]).
  (destruct n; [ simpl; unfold Int.repr; simpl; intro H; inversion H | ]).
  exfalso; apply Nat.nle_succ_0 in Hrange; assumption.
Qed.


Close Scope nat_scope.

Close Scope Z_scope.