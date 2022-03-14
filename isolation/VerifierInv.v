From compcert Require Import Integers Values.
From bpf.comm Require Import Regs State LemmaNat.
From bpf.model Require Import Semantics.
From bpf.isolation Require Import AlignChunk CommonISOLib.
From Coq Require Import ZArith Lia List.
Import ListNotations.

Open Scope Z_scope.

Ltac destruct_if_zeqb Hname :=
  match goal with
  | |- context [(if ?X then _ else _) = Some _] =>
    destruct X eqn: Hname;
    [ eexists; rewrite Z.eqb_eq in Hname; rewrite Hname;
  reflexivity |
      rewrite Z.eqb_neq in Hname]
  end.

(**r CertrBPF needs the following two properties guaranteed by an assumed rbpf verifier, we will implement a verified verifier later~

\begin{enumerate}
    \item dst \& src registers are in [0, 10].
    \item all jump operations are always within in bound.
    tbc...
    \item when ins.opcode = div, ins.src != 0
    \item when ins.opcode = shift (lsh/rsh/arsh), $0 \leq ins.src \leq 32/64$
    \item etc... (more ambitious: {\color{red} check\_mem = true?}  ...)  
\end{enumerate}

 *)

Definition well_dst (i: int64) : Prop :=
  0 <= get_dst i <= 10.

Definition well_src (i: int64) : Prop :=
  0 <= get_src i <= 10.

Definition well_list_range (l: list int64) : Prop :=
  (**r (0, Int.max_unsigned/8): at least one instruction, and at most Int.max_unsigned/8 because of memory region *)
  1 <= Z.of_nat (List.length l) /\
  Z.of_nat (List.length l) * 8 <= Ptrofs.max_unsigned /\
  (**r the last instruaction is always exit: to guarantee the next instruction of each instruction is within the bound *)
  List.nth_error l (List.length l - 1) = Some (Int64.repr 0x95).

(**r how to define valid instruction: according to its opcode? any other more efficient algorithms? *) (*
Definition valid_instruction () *)

Close Scope Z_scope.

Open Scope nat_scope.

Definition is_jump (i: int64) : bool :=
  match get_opcode i with
  | 0x05
  | 0x15 | 0x1d
  | 0x25 | 0x2d
  | 0x35 | 0x3d
  | 0xa5 | 0xad
  | 0xb5 | 0xbd
  | 0x45 | 0x4d
  | 0x55 | 0x5d
  | 0x65 | 0x6d
  | 0x75 | 0x7d
  | 0xc5 | 0xcd
  | 0xd5 | 0xdd => true
  | _    => false
  end.

Definition is_lddw (i: int64) : bool :=
  match get_opcode i with
  | 0x18 => true
  | _    => false
  end.

Definition well_jump (i: int64) (pc len: nat) : Prop :=
  if is_jump i then
    let imm := Regs.get_offset i in
    let pc'  :=Int.add (Int.repr (Z.of_nat pc)) imm in
      Int.cmpu Clt pc' (Int.repr (Z.of_nat len)) = true
  else
    True.

Definition well_lddw (i: int64) (pc len: nat) : Prop :=
  if is_lddw i then
    Int.cmpu Clt (Int.add (Int.repr (Z.of_nat pc)) Int.one) (Int.repr (Z.of_nat len)) = true
  else
    True.

Definition verifier_inv' (l: list int64): Prop :=
  well_list_range l /\
  forall i, i < List.length l ->
    match List.nth_error l i with
    | Some ins =>
        well_dst ins /\ well_src ins /\
        well_lddw ins i (List.length l) /\
        well_jump ins i (List.length l)
    | None => False
    end.

Definition verifier_inv (st: state): Prop :=
  (ins_len st) = (List.length (ins st))  /\
  verifier_inv' (ins st).

Close Scope nat_scope.

Lemma verifier_inv_dst_reg:
  forall ins,
    well_dst ins ->
    exists r,
      Regs.int64_to_dst_reg' ins = Some r.
Proof.
  unfold well_dst, Regs.int64_to_dst_reg'; intros.
  unfold z_to_reg.
  remember (get_dst ins) as i.
  clear Heqi.
  destruct_if_zeqb Heq0.
  destruct_if_zeqb Heq1.
  destruct_if_zeqb Heq2.
  destruct_if_zeqb Heq3.
  destruct_if_zeqb Heq4.
  destruct_if_zeqb Heq5.
  destruct_if_zeqb Heq6.
  destruct_if_zeqb Heq7.
  destruct_if_zeqb Heq8.
  destruct_if_zeqb Heq9.
  destruct_if_zeqb Heq10.
  lia.
Qed.


Lemma verifier_inv_src_reg :
  forall ins,
    well_src ins ->
    exists r,
      Regs.int64_to_src_reg' ins = Some r.
Proof.
  unfold well_src, Regs.int64_to_src_reg'; intros.
  unfold z_to_reg.
  remember (get_src ins) as i.
  clear Heqi.
  destruct_if_zeqb Heq0.
  destruct_if_zeqb Heq1.
  destruct_if_zeqb Heq2.
  destruct_if_zeqb Heq3.
  destruct_if_zeqb Heq4.
  destruct_if_zeqb Heq5.
  destruct_if_zeqb Heq6.
  destruct_if_zeqb Heq7.
  destruct_if_zeqb Heq8.
  destruct_if_zeqb Heq9.
  destruct_if_zeqb Heq10.
  lia.
Qed.

Lemma opcode_and_255:
  forall ins,
    Nat.land (get_opcode ins) 255 = get_opcode ins.
Proof.
  intros.
  unfold get_opcode.
  unfold Int64.and.
  change (Int64.unsigned (Int64.repr 255)) with (Z.of_nat (Z.to_nat 255)).
  assert (Heq: Z.of_nat (Z.to_nat (Int64.unsigned ins)) = Int64.unsigned ins).
  {
    rewrite Z2Nat.id.
    reflexivity.
    apply Int64_unsigned_ge_0.
  }
  rewrite <- Heq; clear Heq.
  rewrite land_land.
  change (Z.to_nat 255) with 255%nat.
  assert (Hrange: (Nat.land (Z.to_nat (Int64.unsigned ins)) 255 <= 255)%nat). {
    rewrite Nat.land_comm.
    rewrite land_bound.
    lia.
  }
  assert (Hrange_z: (Z.of_nat (Nat.land (Z.to_nat (Int64.unsigned ins)) 255%nat) <= 255)%Z) by lia.
  rewrite Int64.unsigned_repr.
  rewrite Nat2Z.id.
  rewrite <- Nat.land_assoc.
  rewrite Nat.land_diag.
  reflexivity.
  change Int64.max_unsigned with 18446744073709551615%Z.
  lia.
Qed.