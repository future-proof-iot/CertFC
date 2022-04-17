From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.
From bpf.verifier.simulation Require Import correct_is_well_src correct_is_not_div_by_zero correct_is_shift_range.


(**
Check bpf_verifier_opcode_alu32_reg.
bpf_verifier_opcode_alu32_reg
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Lemma bpf_verifier_opcode_alu32_reg_match:
  forall c
  (Halu : match c with
     | 12%nat => ADD32_REG
     | 28%nat => SUB32_REG
     | 44%nat => MUL32_REG
     | 60%nat => DIV32_REG
     | 76%nat => OR32_REG
     | 92%nat => AND32_REG
     | 108%nat => LSH32_REG
     | 124%nat => RSH32_REG
     | 156%nat => MOD32_REG
     | 172%nat => XOR32_REG
     | 188%nat => MOV32_REG
     | 204%nat => ARSH32_REG
     | _ => ALU32_REG_ILLEGAL
     end = ALU32_REG_ILLEGAL),
      12  <> (Z.of_nat c) /\
      28  <> (Z.of_nat c) /\
      44  <> (Z.of_nat c) /\
      60  <> (Z.of_nat c) /\
      76  <> (Z.of_nat c) /\
      92  <> (Z.of_nat c) /\
      108 <> (Z.of_nat c) /\
      124 <> (Z.of_nat c) /\
      156 <> (Z.of_nat c) /\
      172 <> (Z.of_nat c) /\
      188 <> (Z.of_nat c) /\
      204 <> (Z.of_nat c).
Proof.
  intros.
  do 205 (destruct c; [inversion Halu; split_conj | ]).
  change 12  with (Z.of_nat 12%nat).
  change 28  with (Z.of_nat 28%nat).
  change 44  with (Z.of_nat 44%nat).
  change 60  with (Z.of_nat 60%nat).
  change 76  with (Z.of_nat 76%nat).
  change 92  with (Z.of_nat 92%nat).
  change 108 with (Z.of_nat 108%nat).
  change 124 with (Z.of_nat 124%nat).
  change 156 with (Z.of_nat 156%nat).
  change 172 with (Z.of_nat 172%nat).
  change 188 with (Z.of_nat 188%nat).
  change 204 with (Z.of_nat 204%nat).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.

Section Bpf_verifier_opcode_alu32_reg.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_alu32_reg.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_alu32_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (opcode_correct x))
     (dcons (fun x => StateLess _ (int64_correct x))
      (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x => StateLess _ (bool_correct x).

Ltac correct_forward L :=
  match goal with
  | |- @correct_body _ _ _ (bindM ?F1 ?F2)  _
                     (Ssequence
                        (Ssequence
                           (Scall _ _ _)
                           (Sset ?V ?T))
                        ?R)
                     _ _ _ _ _ _ _ =>
      eapply L;
      [ change_app_for_statement ;
        let b := match T with
                 | Ecast _ _ => constr:(true)
                 | _         => constr:(false)
                 end in
        eapply correct_statement_call with (has_cast := b)
      |]
  | |- @correct_body _ _ _ (match  ?x with true => _ | false => _ end) _
                     (Sifthenelse _ _ _)
                     _ _ _ _ _ _ _ =>
      eapply correct_statement_if_body; [prove_in_inv | destruct x ]
  end.

  Instance correct_function_bpf_verifier_opcode_alu32_reg : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_alu32_reg.
    simpl. (*
    unfold nat_to_opcode_alu32_reg. *)
    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD32 => bindM (upd_reg ... *)
    unfold INV.
    destruct nat_to_opcode_alu32_reg eqn: Halu. (**r case discussion on each alu32_instruction *)
    - (**r ADD32_REG *)
      eapply correct_statement_switch with (n:= 12).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 12%nat). {
          clear - Halu.
          do 12 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 192 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 12) with 12 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r SUB32_REG *)
      eapply correct_statement_switch with (n:= 28).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 28%nat). {
          clear - Halu.
          do 28 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 176 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 28) with 28 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MUL32_REG *)
      eapply correct_statement_switch with (n:= 44).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 44%nat). {
          clear - Halu.
          do 44 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 160 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 44) with 44 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r DIV32_REG *)
      eapply correct_statement_switch with (n:= 60).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 60%nat). {
          clear - Halu.
          do 60 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 144 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 60) with 60 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r OR32_REG *)
      eapply correct_statement_switch with (n:= 76).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 76%nat). {
          clear - Halu.
          do 76 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 128 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 76) with 76 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r AND32_REG *)
      eapply correct_statement_switch with (n:= 92).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 92%nat). {
          clear - Halu.
          do 92 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 112 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 92) with 92 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LSH32_REG *)
      eapply correct_statement_switch with (n:= 108).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 108%nat). {
          clear - Halu.
          do 108 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 96 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 108) with 108 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RSH32_REG *)
      eapply correct_statement_switch with (n:= 124).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 124%nat). {
          clear - Halu.
          do 124 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 80 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 124) with 124 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOD32_REG *)
      eapply correct_statement_switch with (n:= 156).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 156%nat). {
          clear - Halu.
          do 156 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 48 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 156) with 156 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r XOR32_REG *)
      eapply correct_statement_switch with (n:= 172).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 172%nat). {
          clear - Halu.
          do 172 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 32 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 172) with 172 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOV32_REG *)
      eapply correct_statement_switch with (n:= 188).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 188%nat). {
          clear - Halu.
          do 188 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 188) with 188 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ARSH32_REG *)
      eapply correct_statement_switch with (n:= 204).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward correct_statement_seq_body_nil.

        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.


        reflexivity.
        reflexivity.
        reflexivity.
        prove_in_inv.
        prove_in_inv.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold correct_is_well_src.match_res in c1.
        unfold match_res.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity|].
        split; [assumption|].
        unfold eval_inv, bool_correct in c1.
        rewrite c1.
        split.
        unfold Cop.sem_cast; simpl.
        destruct x; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_reg in Halu.
        assert (Hc_eq: c = 204%nat). {
          clear - Halu.
          do 204 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 204) with 204 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ALU32_REG_ILLEGAL *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold eval_inv, opcode_correct in c1.
        destruct c1 as (c1 & Hc1_range).
        exists (Z.of_nat c).
        split.
        unfold exec_expr.
        rewrite p0.
        rewrite c1.
        reflexivity.
        split.

        change Int.modulus with 4294967296.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        unfold nat_to_opcode_alu32_reg in Halu.
        apply bpf_verifier_opcode_alu32_reg_match in Halu.
        destruct Halu as (Hfirst & Halu). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Halu; rewrite Halu; clear Halu.
        (* default *)
        simpl.
        eapply correct_statement_seq_body_drop.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        exists (Vint (Int.repr 0)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
Qed.

End Bpf_verifier_opcode_alu32_reg.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_alu32_reg.
