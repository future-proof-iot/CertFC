From compcert Require Import Integers.
From bpf.comm Require Import LemmaNat.
From bpf.monadicmodel Require Import Opcode.
From Coq Require Import Lia ZArith.

Open Scope Z_scope.

Lemma nat8_land_240_255_eq:
  forall (n:nat)
    (Hnat8: (n <= 255)%nat),
    (Int.and (Int.and (Int.repr (Z.of_nat n)) (Int.repr 240)) (Int.repr 255)) = Int.repr (Z.of_nat (Nat.land n 240)).
Proof.
  intros.
  rewrite Int.and_assoc.
  change (Int.and (Int.repr 240) (Int.repr 255)) with (Int.repr 240).
  unfold Int.and.
  f_equal.
  rewrite! Int.unsigned_repr_eq.
  change (240 mod Int.modulus) with 240.
  rewrite Zmod_small.
  change 240 with (Z.of_nat 240%nat).
  rewrite land_land. reflexivity.
  change Int.modulus with 4294967296.
  lia.
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

Lemma opcode_alu64_eqb_eq : forall a b,
    opcode_alu64_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_alu64 :
  forall (E: nat -> opcode_alu64)
         (F: nat -> opcode_alu64) n,
    ((fun n => opcode_alu64_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_alu64_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_alu64_if_same:
  forall (op: nat),
    byte_to_opcode_alu64 op = byte_to_opcode_alu64_if op.
Proof.
  intros.
  unfold byte_to_opcode_alu64, byte_to_opcode_alu64_if.
  apply opcode_alu64_eqb_eq.
  match goal with
  | |- ?A = true => set (P := A)
  end.
  pattern (Nat.land op 240) in P.
  match goal with
  | P := ?F (Nat.land op 240) |- _=>
      apply (Forall_exec_spec F 240)
  end.
  destruct (op =? 135).
  vm_compute.
  reflexivity.
  vm_compute.
  reflexivity.
  rewrite Nat.land_comm.
  apply land_bound.
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

Lemma opcode_branch_eqb_eq : forall a b,
    opcode_branch_eqb a b = true -> a = b.
Proof.
  destruct a,b ; simpl ;congruence.
Qed.

Lemma lift_opcode_branch :
  forall (E: nat -> opcode_branch)
         (F: nat -> opcode_branch) n,
    ((fun n => opcode_branch_eqb (E n) (F n) = true) n) <->
      (((fun n => opcode_branch_eqb (E n) (F n)) n) = true).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma byte_to_opcode_branch_if_same:
  forall (op: nat),
    byte_to_opcode_branch op = byte_to_opcode_branch_if op.
Proof.
  intros.
  unfold byte_to_opcode_branch, byte_to_opcode_branch_if.
  apply opcode_branch_eqb_eq.
  match goal with
  | |- ?A = true => set (P := A)
  end.
  pattern (Nat.land op 240) in P.
  match goal with
  | P := ?F (Nat.land op 240) |- _=>
      apply (Forall_exec_spec F 240)
  end.
  destruct (op =? 5); destruct (op =? 149).
  all: try (vm_compute; reflexivity).
  rewrite Nat.land_comm.
  apply land_bound.
Qed.

Lemma nat8_neq_135:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 135),
      Int.repr (Z.of_nat n) <> Int.repr 135.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  change Int.modulus with 4294967296%Z.
  lia.
Qed.

Lemma nat8_neq_5:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 5),
      Int.repr (Z.of_nat n) <> Int.repr 5.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  change Int.modulus with 4294967296%Z.
  lia.
Qed.


Lemma nat8_neq_149:
  forall n
    (Hrange : n <= 255)
    (Hc2_eq : n <> 149),
      Int.repr (Z.of_nat n) <> Int.repr 149.
Proof.
  repeat intro.
  Transparent Int.repr.
  unfold Int.repr in *.
  inversion H.
  rewrite Int.Z_mod_modulus_eq in H1.
  rewrite Zmod_small in H1.
  lia.
  change Int.modulus with 4294967296%Z.
  lia.
Qed.


Ltac simpl_if Ht :=
  match goal with
  | |- context [if ?X then _ else _] =>
    destruct X eqn: Ht; [rewrite Nat.eqb_eq in Ht | rewrite Nat.eqb_neq in Ht]
  end.

Ltac simpl_opcode Hop := simpl_if Hop; [rewrite Hop; intuition | ].

Ltac simpl_land HOP:=
  match goal with
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y <> ?W) /\ _ =>
      split; [intro HOP; rewrite H in HOP; inversion HOP |]
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y = ?W -> _) /\ _ =>
      split; [intro HOP; rewrite H in HOP; inversion HOP |]
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y <> ?W) =>
      intro HOP; rewrite H in HOP; inversion HOP
  | H: Nat.land ?X ?Y = ?Z |- (Nat.land ?X ?Y = ?W -> _) =>
      intro HOP; rewrite H in HOP; inversion HOP
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y <> ?Z) /\ _ =>
      split; [assumption |]
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y <> ?Z) =>
      assumption
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y = ?Z -> _) /\ _ =>
      split; [intro HOP; rewrite HOP in H; exfalso; apply H; reflexivity |]
  | H: Nat.land ?X ?Y <> ?Z |- (Nat.land ?X ?Y = ?Z -> _) =>
      intro HOP; rewrite HOP in H; exfalso; apply H; reflexivity
  end.

Close Scope Z_scope.