(**r: equivalence between bpf.model (with formal syntax + semantics) and bpf.src (for dx) *)

From Coq Require Import Logic.FunctionalExtensionality ZArith Lia.
From compcert Require Import Integers Values Memory Memdata.

From bpf.comm Require Import State Monad LemmaNat.
From bpf.src Require Import DxInstructions.

From bpf.model Require Import Semantics.
From bpf.monadicmodel Require Import Opcode.

From bpf.equivalence Require Import switch.

Open Scope Z_scope.

Ltac unfold_monad :=
  match goal with
  | |- _ =>
    unfold bindM, returnM
  end.

Ltac unfold_dx_type :=
  match goal with
  | |- _ =>
    unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag, DxMonad.eval_ins;
    unfold int64_to_opcode;
    unfold DxIntegers.sint32_t, DxIntegers.int64_t, DxNat.nat8, DxValues.val64_t, DxValues.valu32_t, DxValues.vals32_t;
  unfold decodeM;
  unfold_monad
  end.

Ltac unfold_dx_name :=
  match goal with
  | |- _ =>
    unfold DxNat.nat8_zero, DxNat.nat8_0x08, DxNat.nat8_0x07, DxIntegers.int64_0xff, DxIntegers.int64_32, DxNat.nat8_0xf0, DxIntegers.int64_64, DxValues.val32_64, DxIntegers.int64_48, DxNat.nat8_0xff, DxValues.val64_zero, Regs.val64_zero, DxIntegers.int32_0, DxIntegers.int32_64
  end.

Ltac unfold_dx :=
  match goal with
  | |- _ =>
    unfold get_opcode_ins, get_opcode, byte_to_opcode;
    unfold_dx_name; unfold_dx_type
  end.

Lemma Int64_unsigned_ge_0:
  forall n,
    0 <= Int64.unsigned n.
Proof.
  intros.
  assert (H: 0 <= Int64.unsigned n < Int64.modulus) by apply Int64.unsigned_range.
  lia.
Qed.

Open Scope nat_scope.

Ltac compute_land :=
  match goal with
  | |- context[match Nat.land ?X ?Y with | _ => _ end] =>
      let x := eval compute in (Nat.land X Y) in
      replace (Nat.land X Y) with x by reflexivity;
      try rewrite Nat.eqb_refl
  | |- context[if (?Z =? Nat.land ?X ?Y) then ?TT else ?FF] =>
      let x := (eval compute in (Z =? Nat.land X Y)) in
        match x with
        | true => TT
        | false => FF
        end
  end.

Ltac compute_if :=
  match goal with
  | |- context[(if ?X then _ else _) = (if ?X then _ else _)] =>
    destruct (X); [| reflexivity]
  | |- context[(if ?X then _ else _) ] =>
    destruct (X); [| reflexivity]
  end.

Ltac Hopcode_solve HOP OP NAME :=
  match goal with
  | |- _ =>
    destruct (HOP =? OP) eqn: Hins;[apply Nat.eqb_eq in Hins; unfold_dx; rewrite Hins; repeat compute_land; simpl;
        try compute_if | apply Nat.eqb_neq in Hins];
  rename Hins into NAME
  end.

Ltac change_int_zero :=
  match goal with
  | |- context [if Int.eq Int.zero ?X then _ else _] =>
    change X with Int.zero;
    rewrite Int.eq_true
  end.

Ltac Hopcode_solve_imm HOP OP VALOP NAME :=
  let Hins := fresh "Hins" in
  match goal with
  | |- _ =>
    destruct (HOP =? OP) eqn: Hins;[apply Nat.eqb_eq in Hins; unfold_dx; rewrite Hins;
    try(
        repeat compute_land; simpl;
        unfold State.upd_reg, upd_reg;
        change_int_zero;
        destruct (VALOP _ _); try reflexivity) | apply Nat.eqb_neq in Hins];
  rename Hins into NAME
  end.

Ltac change_int_8 :=
  match goal with
  | |- context [if Int.eq Int.zero ?X then _ else _] =>
    change X with (Int.repr 8);
    change (Int.eq Int.zero (Int.repr 8)) with false;
    simpl
  end.

Ltac Hopcode_solve_reg HOP OP VALOP NAME :=
  let Hins := fresh "Hins" in
  match goal with
  | |- _ =>
    destruct (HOP =? OP) eqn: Hins;[apply Nat.eqb_eq in Hins; unfold_dx; rewrite Hins;
    try(
        repeat compute_land; simpl;
        unfold State.upd_reg, upd_reg;
        change_int_8;
        destruct (VALOP _ _); try reflexivity) | apply Nat.eqb_neq in Hins];
  rename Hins into NAME
  end.

Ltac Hopcode_solve_jump HOP OP NAME :=
  match goal with
  | |- _ =>
    Hopcode_solve HOP OP NAME;
    [ unfold DxMonad.upd_pc, DxIntegers.int64_32, DxIntegers.int64_48;
  reflexivity | idtac]
  end.

Ltac Hopcode_solve_alu32_imm HOP OP NAME :=
  match goal with
  | |- _ =>
    Hopcode_solve HOP OP NAME; 
    [ change_int_zero;
      try unfold rBPFValues.sint32_to_vint;
      unfold upd_reg;
      destruct Val.longofintu; try reflexivity | idtac]
  end.

Ltac Hopcode_solve_alu32_reg HOP OP NAME :=
  match goal with
  | |- _ =>
    Hopcode_solve HOP OP NAME;
    [ change_int_8;
      try unfold rBPFValues.sint32_to_vint;
      unfold upd_reg;
      destruct Val.longofintu; try reflexivity | idtac]
  end.


Ltac Hopcode_simpl :=
  match goal with
  | H :  ?X <> ?X |- _ =>
    exfalso; apply H; reflexivity
  | |- _ => repeat compute_land; unfold eval_ins_len; reflexivity
  end.

Lemma opcode_le_255_Z :
  forall st,
   (0 <= Int64.unsigned
                  (Int64.and (Int64.repr 255) (State.eval_ins (State.eval_pc st) st)) <= 255)%Z.
Proof.
  intros.
  split.
  - assert (H64_unsigned: forall i, (0 <= Int64.unsigned i <= Int64.max_unsigned)%Z). {
      apply Int64.unsigned_range_2.
    }
    specialize (H64_unsigned (Int64.and (Int64.repr 255%Z) (State.eval_ins (State.eval_pc st) st))).
    lia.
  -
    assert (Ht: ((Int64.unsigned (Int64.repr 255)) = 255)%Z).
    rewrite <- Int64.unsigned_repr; [reflexivity | idtac].
    unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
    simpl; lia.
    rewrite <- Ht.
    apply Int64.and_le.
Qed.

Lemma opcode_le_255 :
  forall st,
    (Z.to_nat (Int64.unsigned
                  (Int64.and (State.eval_ins (State.eval_pc st) st) (Int64.repr 255))))%Z <= 255.
Proof.
  intros.
  rewrite Int64.and_commut.
  assert (H255: Z.to_nat 255%Z = 255). { reflexivity. }
  rewrite <- H255; clear H255.
  (*assert (H0: Z.to_nat 0%Z = 0). { reflexivity. }
  rewrite <- H0. *)
  assert (H : (0 <= Int64.unsigned
                  (Int64.and (Int64.repr 255) (State.eval_ins (State.eval_pc st) st)) <= 255)%Z). { apply opcode_le_255_Z. }
  destruct H.
  apply Z2Nat.inj_le; try lia.
Qed.

Lemma equivalence_between_formal_and_dx_step:
  (*forall st, st = returnS -> *)
  Semantics.step = DxInstructions.step.
Proof.
  unfold Semantics.step, DxInstructions.step.
  unfold_dx.
  apply functional_extensionality.
  intros.
  unfold eval_pc.
  unfold eval_ins.
  unfold Decode.decode.
  compute_if.
  unfold get_dst, DxMonad.int64_to_dst_reg, int64_to_dst_reg.
  unfold Regs.int64_to_dst_reg', Regs.int64_to_src_reg'. TBC.
  destruct Regs.z_to_reg eqn: Hdst; [].
  rewrite switch_if_same.
  unfold get_instruction_if, Decode.get_instruction, Regs.get_opcode.
  remember (Z.to_nat
      (Int64.unsigned
         (Int64.and (State.eval_ins (State.eval_pc x) x) (Int64.repr 255)))) as Hopcode.
  unfold DxInstructions.get_immediate, Regs.get_immediate, eval_immediate, step_alu_binary_operation, eval_src, eval_reg, get_dst, get_src64, get_src32, step_opcode_alu64, step_opcode_alu32, get_opcode_alu64, get_opcode_alu32, byte_to_opcode_alu64, byte_to_opcode_alu32, rBPFValues.val64_divlu, rBPFValues.val64_modlu, rBPFValues.val32_divu, rBPFValues.val32_modu, step_opcode_mem_ld_reg, step_load_x_operation, get_opcode_mem_ld_reg, byte_to_opcode_mem_ld_reg, step_opcode_mem_ld_imm, get_opcode_mem_ld_imm, byte_to_opcode_mem_ld_imm, Regs.get_offset, step_opcode_branch, get_opcode_branch, byte_to_opcode_branch, Regs.get_offset, State.upd_reg, upd_reg, DxMonad.exec_function; unfold_dx.


  assert (Hopcode_range: Hopcode <= 255). {
    rewrite HeqHopcode.
    apply opcode_le_255.
  }
  assert (Heq: Nat.land
      (Z.to_nat
         (Z.land
            (Int.unsigned
               (Int.repr
                  (Int64.unsigned
                     (Int64.and (State.eval_ins (State.eval_pc x) x)
                        (Int64.repr 255))))) 255)) 7 = Nat.land Hopcode 7). {
    rewrite HeqHopcode.
    unfold Int64.and.
    change (Int64.unsigned (Int64.repr 255)) with (Z.of_nat 255).
    change 255%Z with (Z.of_nat 255).
    assert (H : Int64.unsigned (State.eval_ins (State.eval_pc x) x) = Z.of_nat (Z.to_nat (Int64.unsigned (State.eval_ins (State.eval_pc x) x)))) by (rewrite Z2Nat.id; [reflexivity | apply Int64_unsigned_ge_0]).
    rewrite H; rewrite land_land; clear H.
    assert (H: 0<= (Nat.land
                        (Z.to_nat
                           (Int64.unsigned
                              (State.eval_ins (State.eval_pc x) x)))
                        255) <= 255). {
      split; [lia | rewrite Nat.land_comm; rewrite land_bound; lia].
    }
    rewrite Int64.unsigned_repr; [| change Int64.max_unsigned with 18446744073709551615%Z; lia].
    rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
    rewrite land_land.
    rewrite <- Nat.land_assoc.
    rewrite Nat.land_diag.
    reflexivity.
  }
  rewrite Heq; clear Heq.
  assert (Heq: Z.to_nat
                   (Z.land
                      (Int.unsigned
                         (Int.repr
                            (Int64.unsigned
                               (Int64.and
                                  (State.eval_ins (State.eval_pc x) x)
                                  (Int64.repr 255))))) 255) = Hopcode). {
    rewrite HeqHopcode.
    unfold Int64.and.
    change (Int64.unsigned (Int64.repr 255)) with (Z.of_nat 255).
    change 255%Z with (Z.of_nat 255).
    assert (H : Int64.unsigned (State.eval_ins (State.eval_pc x) x) = Z.of_nat (Z.to_nat (Int64.unsigned (State.eval_ins (State.eval_pc x) x)))) by (rewrite Z2Nat.id; [reflexivity | apply Int64_unsigned_ge_0]).
    rewrite H; rewrite land_land; clear H.
    assert (H: 0<= (Nat.land
                        (Z.to_nat
                           (Int64.unsigned
                              (State.eval_ins (State.eval_pc x) x)))
                        255) <= 255). {
      split; [lia | rewrite Nat.land_comm; rewrite land_bound; lia].
    }
    rewrite Int64.unsigned_repr; [| change Int64.max_unsigned with 18446744073709551615%Z; lia].
    rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
    rewrite land_land.
    rewrite <- Nat.land_assoc.
    rewrite Nat.land_diag.
    reflexivity.
  }
  rewrite Heq; clear Heq.
  clear HeqHopcode.

  (**r ADD64i *)
  Hopcode_solve_imm Hopcode 0x07 Val.addl Hadd64i.

  (**r Add64r *)
  Hopcode_solve_reg Hopcode 0x0f Val.addl Hadd64r.

  (**r SUB64i *)
  Hopcode_solve_imm Hopcode 0x17 Val.subl Hsub64i.

  (**r SUB64r *)

  Hopcode_solve_reg Hopcode 0x1f Val.subl Hsub64r.

  (**r mul64i *)
  Hopcode_solve_imm Hopcode 0x27 Val.mull Hmul64i.


  (**r Hmul64r *)

  Hopcode_solve_reg Hopcode 0x2f Val.mull Hmul64r.

  (**r Hdiv64i *)
  Hopcode_solve Hopcode 0x37 Hdiv64i.

  change_int_zero.
  unfold rBPFValues.compl_ne, DxValues.Val_ulongofslong.
  destruct (negb _); [| reflexivity].

  unfold upd_reg.
  destruct (Val.divlu _ _); try reflexivity.
  destruct v; try reflexivity.

  (**r Hdiv64r *)
  Hopcode_solve Hopcode 0x3f Hdiv64r.
  change_int_8.
  destruct (rBPFValues.compl_ne); [| reflexivity].
  unfold upd_reg.
  destruct (Val.divlu _ _); try reflexivity.
  destruct v; try reflexivity.

  (**r Hor64i *)
  Hopcode_solve_imm Hopcode 0x47 Val.orl Hor64i.

  (**r Hor64r *)
  Hopcode_solve_reg Hopcode 0x4f Val.orl Hor64r.

  (**r Hand64i *)
  Hopcode_solve_imm Hopcode 0x57 Val.andl Hand64i.

  (**r Hand64r *)
  Hopcode_solve_reg Hopcode 0x5f Val.andl Hand64r.

  (**r Hlsh64i *)
  Hopcode_solve Hopcode 0x67 Hlsh64i.

  change_int_zero.
  unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu, DxValues.Val_ulongofslong.
  destruct (Int.ltu _ _); [ |reflexivity].

  unfold upd_reg.
  destruct (Val.shll _ _); try reflexivity.

  (**r Hlsh64r *)
  Hopcode_solve Hopcode 0x6f Hlsh64r.
  change_int_8.
  destruct (rBPFValues.compu_lt_32 _ _); [ |reflexivity].

  unfold upd_reg.
  destruct (Val.shll _ _); try reflexivity.

  (**r Hrsh64i *)
  Hopcode_solve Hopcode 0x77 Hrsh64i.
  change_int_zero.
  unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu, DxValues.Val_ulongofslong.
  destruct (Int.ltu _ _); [ |reflexivity].

  unfold upd_reg.
  destruct (Val.shrlu _ _); try reflexivity.

  (**r Hrsh64r *)
  Hopcode_solve Hopcode 0x7f Hrsh64r.
  change_int_8.
  destruct (rBPFValues.compu_lt_32 _ _); [ |reflexivity].

  unfold upd_reg.
  destruct (Val.shrlu _ _); try reflexivity.

  (**r Hneg64 *)
  Hopcode_solve_imm Hopcode 0x87 Val.negl Hneg64.
  repeat compute_land; simpl.

  unfold upd_reg;
  destruct (Val.negl _); try reflexivity.

  (**r Hmod64i *)

  Hopcode_solve Hopcode 0x97 Hmod64i.
  change_int_zero.
  unfold rBPFValues.compl_ne, DxValues.Val_ulongofslong.
  destruct (negb _); [| reflexivity].

  unfold upd_reg.
  destruct (Val.modlu _ _); try reflexivity.
  destruct v; try reflexivity.

  (**r Hmod64r *)
  Hopcode_solve Hopcode 0x9f Hmod64r.
  change_int_8.
  destruct (rBPFValues.compl_ne _ _); [| reflexivity].
  unfold upd_reg.
  destruct (Val.modlu _ _); try reflexivity.
  destruct v; try reflexivity.

  (**r Hxor64i *)
  Hopcode_solve_imm Hopcode 0xa7 Val.xorl Hxor64i.

  (**r Hor64r *)
  Hopcode_solve_reg Hopcode 0xaf Val.xorl Hxor64r.

  (**r Hmov64i *)
  Hopcode_solve Hopcode 0xb7 Hmov64i.
  change_int_zero.
  reflexivity.


  (**r Hmov64r *)
  Hopcode_solve Hopcode 0xbf Hmov64r.
  change_int_8.
  unfold upd_reg.
  destruct (State.eval_reg _ _); try reflexivity.

  (**r Harsh64i *)
  Hopcode_solve Hopcode 0xc7 Harsh64i.
  change_int_zero.
  unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu, DxValues.Val_ulongofslong.
  destruct (Int.ltu _ _); [ |reflexivity].

  unfold upd_reg.
  destruct (Val.shrl _ _); try reflexivity.

  (**r Harsh64r *)
  Hopcode_solve Hopcode 0xcf Harsh64r.
  change_int_8.
  destruct (rBPFValues.compu_lt_32 _ _); [ |reflexivity].

  unfold upd_reg.
  destruct (Val.shrl _ _); try reflexivity.

(*ALU32*)

  (**r Hadd32i *)
  Hopcode_solve_alu32_imm Hopcode 0x04 Hadd32i.

  (**r Hadd32r *)
  Hopcode_solve_alu32_reg Hopcode 0x0c Hadd32r.

  (**r Hsub32i *)
  Hopcode_solve_alu32_imm Hopcode 0x14 Hsub32i.

  (**r Hsub32r *)
  Hopcode_solve_alu32_reg Hopcode 0x1c Hsub32r.

  (**r Hmul32i *)
  Hopcode_solve_alu32_imm Hopcode 0x24 Hmul32i.

  (**r Hmul32r *)
  Hopcode_solve_alu32_reg Hopcode 0x2c Hmul32r.

  (**r Hdiv32i *)
  Hopcode_solve Hopcode 0x34 Hdiv32i.

  change_int_zero.
  unfold rBPFValues.comp_ne_32, rBPFValues.sint32_to_vint, DxValues.val32_zero.
  unfold DxIntegers.int32_0.
  destruct negb; try reflexivity.
  destruct Val.divu; try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hdiv32r *)
  Hopcode_solve Hopcode 0x3c Hdiv32r.

  change_int_8.
  unfold DxIntegers.int32_0.
  destruct rBPFValues.comp_ne_32; try reflexivity.
  destruct Val.divu; try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hor32i *)
  Hopcode_solve_alu32_imm Hopcode 0x44 Hor32i.

  (**r Hor32r *)
  Hopcode_solve_alu32_reg Hopcode 0x4c Hor32r.

  (**r Hand32i *)
  Hopcode_solve_alu32_imm Hopcode 0x54 Hand32i.

  (**r Hand32r *)
  Hopcode_solve_alu32_reg Hopcode 0x5c Hand32r.

  (**r Hlsh32i *)
  Hopcode_solve Hopcode 0x64 Hlsh32i.
  change_int_zero.
  unfold rBPFValues.compu_lt_32, rBPFValues.sint32_to_vint, DxValues.val32_32.
  unfold DxIntegers.int32_32.
  destruct (Int.ltu _ _); try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hlsh32r *)
  Hopcode_solve Hopcode 0x6c Hlsh32r.
  change_int_8.
  unfold DxValues.val32_32, DxIntegers.int32_32.
  destruct rBPFValues.compu_lt_32; try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hrsh32i *)
  Hopcode_solve Hopcode 0x74 Hrsh32i.
  change_int_zero.
  unfold rBPFValues.compu_lt_32, rBPFValues.sint32_to_vint, DxValues.val32_32.
  unfold DxIntegers.int32_32.
  destruct (Int.ltu _ _); try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hrsh32r *)
  Hopcode_solve Hopcode 0x7c Hrsh32r.
  change_int_8.
  unfold DxValues.val32_32, DxIntegers.int32_32.
  destruct rBPFValues.compu_lt_32; try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hneg32 *)
  Hopcode_solve_alu32_imm Hopcode 0x84 Hneg32.

  (**r Hmod32i *)
  Hopcode_solve Hopcode 0x94 Hmod32i.
  change_int_zero.
  unfold rBPFValues.comp_ne_32, rBPFValues.sint32_to_vint, DxValues.val32_zero.
  unfold DxIntegers.int32_0.
  destruct negb; try reflexivity.
  destruct Val.modu; try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hmod32r *)
  Hopcode_solve Hopcode 0x9c Hmod32r.
  change_int_8.
  unfold DxIntegers.int32_0.
  destruct rBPFValues.comp_ne_32; try reflexivity.
  destruct Val.modu; try reflexivity.
  unfold upd_reg.
  destruct Val.longofintu; try reflexivity.

  (**r Hxor32i *)
  Hopcode_solve_alu32_imm Hopcode 0xa4 Hxor32i.

  (**r Hxor32r *)
  Hopcode_solve_alu32_reg Hopcode 0xac Hxor32r.

  (**r Hmov32i *)
  Hopcode_solve Hopcode 0xb4 Hmov32i.
  change_int_zero.
  reflexivity.

  (**r Hmov32r *)
  Hopcode_solve Hopcode 0xbc Hmov32r.
  change_int_8.
  unfold upd_reg.
  destruct Val.longofintu; reflexivity.

  (**r Harsh32i *)
  Hopcode_solve Hopcode 0xc4 Harsh32i.
  change_int_zero.
  unfold Val.longofint, rBPFValues.val_intuoflongu, rBPFValues.sint32_to_vint.
  unfold rBPFValues.compu_lt_32, Regs.get_immediate, DxValues.val32_32.
  unfold DxIntegers.int32_32.
  destruct (Int.ltu _ _); try reflexivity.
  unfold upd_reg.
  destruct Val.shr; try reflexivity.

  (**r Harsh32r *)
  Hopcode_solve Hopcode 0xcc Harsh32r.
  change_int_8.
  unfold DxValues.val32_32, DxIntegers.int32_32.
  destruct rBPFValues.compu_lt_32; try reflexivity.
  unfold upd_reg.
  destruct Val.longofint; try reflexivity.

  (**r HLDDW *)
  Hopcode_solve Hopcode 0x18 HLDDW.
  reflexivity.

  (**r Hldx32 *)
  Hopcode_solve Hopcode 0x61 Hldx32.

  reflexivity.


  (**r Hldx16 *)
  Hopcode_solve Hopcode 0x69 Hldx16.

  reflexivity.

  (**r Hldx8 *)
  Hopcode_solve Hopcode 0x71 Hldx8.

  reflexivity.

  (**r Hldx64 *)
  Hopcode_solve Hopcode 0x79 Hldx64.

  reflexivity.

  (**r Hstx32 *)
  Hopcode_solve Hopcode 0x62 Hstx32.

  reflexivity.

  (**r Hstx16 *)
  Hopcode_solve Hopcode 0x6a Hstx16.

  reflexivity.

  (**r Hstx8 *)
  Hopcode_solve Hopcode 0x72 Hstx8.

  reflexivity.

  (**r Hstx64 *)
  Hopcode_solve Hopcode 0x7a Hstx64.

  reflexivity.

  (**r Hst32 *)
  Hopcode_solve Hopcode 0x63 Hst32.

  reflexivity.

  (**r Hst16 *)
  Hopcode_solve Hopcode 0x6b Hst16.

  reflexivity.

  (**r Hst8 *)
  Hopcode_solve Hopcode 0x73 Hst8.

  reflexivity.

  (**r Hst64 *)
  Hopcode_solve Hopcode 0x7b Hst64.

  reflexivity.

  (**r Hja *)
  Hopcode_solve_jump Hopcode 0x05 Hja.

  (**r Heqi *)
  Hopcode_solve_jump Hopcode 0x15 Heqi.

  (**r Heqr *)
  Hopcode_solve_jump Hopcode 0x1d Heqr.

  (**r Hgti *)
  Hopcode_solve_jump Hopcode 0x25 Hgti.

  (**r Hgtr *)
  Hopcode_solve_jump Hopcode 0x2d Hgtr.

  (**r Hgei *)
  Hopcode_solve_jump Hopcode 0x35 Hgei.

  (**r Hger *)
  Hopcode_solve_jump Hopcode 0x3d Hger.

  (**r Hlti *)
  Hopcode_solve_jump Hopcode 0xa5 Hlti.

  (**r Hltr *)
  Hopcode_solve_jump Hopcode 0xad Hltr.

  (**r Hlei *)
  Hopcode_solve_jump Hopcode 0xb5 Hlei.

  (**r Hler *)
  Hopcode_solve_jump Hopcode 0xbd Hler.

  (**r Hseti *)
  Hopcode_solve_jump Hopcode 0x45 Hseti.

  (**r Hsetr *)
  Hopcode_solve_jump Hopcode 0x4d Hsetr.

  (**r Hnei *)
  Hopcode_solve_jump Hopcode 0x55 Hnei.

  (**r Hner *)
  Hopcode_solve_jump Hopcode 0x5d Hner.

  (**r Hsgti *)
  Hopcode_solve_jump Hopcode 0x65 Hsgti.

  (**r Hsgtr *)
  Hopcode_solve_jump Hopcode 0x6d Hsgtr.

  (**r Hsgei *)
  Hopcode_solve_jump Hopcode 0x75 Hsgei.

  (**r Hsger *)
  Hopcode_solve_jump Hopcode 0x7d Hsger.

  (**r Hslti *)
  Hopcode_solve_jump Hopcode 0xc5 Hslti.

  (**r Hsltr *)
  Hopcode_solve_jump Hopcode 0xcd Hsltr.

  (**r Hslei *)
  Hopcode_solve_jump Hopcode 0xd5 Hslei.

  (**r Hsler *)
  Hopcode_solve_jump Hopcode 0xdd Hsler.

  (**r Hcall *)
  unfold rBPFValues.int64_to_sint32, rBPFValues.val_intsoflongu.
  Hopcode_solve Hopcode 0x85 Hcall.
  change_int_zero.
  unfold Regs.get_immediate, rBPFValues.int64_to_sint32.
  reflexivity.

  (**r Hret *)
  Hopcode_solve_jump Hopcode 0x95 Hret.
  (**now all we need to proof is the `BPF_ILLEGAL_INS` *)

  do 5 (destruct Hopcode; [Hopcode_simpl | apply le_S_n in Hopcode_range]).
  do 150 (destruct Hopcode; [Hopcode_simpl | apply le_S_n in Hopcode_range]).
  do 100 (destruct Hopcode; [Hopcode_simpl | apply le_S_n in Hopcode_range]).
  clear - Hopcode_range.
  destruct Hopcode.
  - Hopcode_simpl.
  - exfalso.
    apply Nat.nle_succ_0 in Hopcode_range; assumption.
Qed.

Lemma equivalence_between_formal_and_dx_aux:
  forall f,
    Semantics.bpf_interpreter_aux f = DxInstructions.bpf_interpreter_aux f.
Proof.
  unfold Semantics.bpf_interpreter_aux, DxInstructions.bpf_interpreter_aux.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM, DxMonad.eval_ins_len, DxMonad.eval_pc, DxMonad.upd_pc_incr, DxMonad.upd_flag.
  unfold DxIntegers.sint32_t.
  unfold DxIntegers.int32_0.
  rewrite equivalence_between_formal_and_dx_step.
  reflexivity.
Qed.

Theorem equivalence_between_formal_and_dx:
  forall f,
    Semantics.bpf_interpreter f = DxInstructions.bpf_interpreter f.
Proof.
  intros.
  unfold Semantics.bpf_interpreter, DxInstructions.bpf_interpreter.
  unfold DxMonad.bindM, DxMonad.upd_reg, DxMonad.eval_flag, DxMonad.eval_reg, DxMonad.returnM.
  rewrite equivalence_between_formal_and_dx_aux.
  reflexivity.
Qed.

Close Scope Z_scope.