From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.
From bpf.verifier.simulation Require Import correct_bpf_verifier_get_offset correct_is_well_jump correct_is_dst_R0.


(**
Check bpf_verifier_opcode_branch_imm.
bpf_verifier_opcode_branch_imm
     : nat -> nat -> nat -> int64 -> M bool

*)
Open Scope Z_scope.

Lemma bpf_verifier_opcode_branch_imm_match:
  forall c
    (Hbranch : match c with
      | 5%nat => JA_IMM
      | 21%nat => JEQ_IMM
      | 37%nat => JGT_IMM
      | 53%nat => JGE_IMM
      | 69%nat => JSET_IMM
      | 85%nat => JNE_IMM
      | 101%nat => JSGT_IMM
      | 117%nat => JSGE_IMM
      | 133%nat => CALL_IMM
      | 149%nat => RET_IMM
      | 165%nat => JLT_IMM
      | 181%nat => JLE_IMM
      | 197%nat => JSLT_IMM
      | 213%nat => JSLE_IMM
      | _ => JMP_IMM_ILLEGAL_INS
      end = JMP_IMM_ILLEGAL_INS),
        5  <> (Z.of_nat c) /\
        21  <> (Z.of_nat c) /\
        37  <> (Z.of_nat c) /\
        53  <> (Z.of_nat c) /\
        69  <> (Z.of_nat c) /\
        85  <> (Z.of_nat c) /\
        101 <> (Z.of_nat c) /\
        117 <> (Z.of_nat c) /\
        133 <> (Z.of_nat c) /\
        149 <> (Z.of_nat c) /\
        165 <> (Z.of_nat c) /\
        181 <> (Z.of_nat c) /\
        197 <> (Z.of_nat c) /\
        213 <> (Z.of_nat c).
Proof.
  intros.
  do 214 (destruct c; [inversion Hbranch; split_conj | ]).
  change 5   with (Z.of_nat 5%nat).
  change 21  with (Z.of_nat 21%nat).
  change 37  with (Z.of_nat 37%nat).
  change 53  with (Z.of_nat 53%nat).
  change 69  with (Z.of_nat 69%nat).
  change 85  with (Z.of_nat 85%nat).
  change 101 with (Z.of_nat 101%nat).
  change 117 with (Z.of_nat 117%nat).
  change 133 with (Z.of_nat 133%nat).
  change 149 with (Z.of_nat 149%nat).
  change 165 with (Z.of_nat 165%nat).
  change 181 with (Z.of_nat 181%nat).
  change 197 with (Z.of_nat 197%nat).
  change 213 with (Z.of_nat 213%nat).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.

Section Bpf_verifier_opcode_branch_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (nat:Type); (nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_branch_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_branch_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (nat_correct x))
      (dcons (fun x => StateLess _ (nat_correct x))
        (dcons (fun x => StateLess _ (nat_correct x))
          (dcons (fun x => StateLess _ (int64_correct x))
            (DList.DNil _)))).

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

  Instance correct_function_bpf_verifier_opcode_branch_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_branch_imm.
    simpl.
    unfold INV.
    destruct nat_to_opcode_branch_imm eqn: Hbranch. (**r case discussion on each branch_instruction *)
    - (**r JA_IMM *)
      eapply correct_statement_switch with (n:= 5).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 5%nat). {
          clear - Hbranch.
          do 5 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 208 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 5) with 5 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JEQ_IMM *)
      eapply correct_statement_switch with (n:= 21).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 21%nat). {
          clear - Hbranch.
          do 21 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 192 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 21) with 21 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JGT_IMM *)
      eapply correct_statement_switch with (n:= 37).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition .
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 37%nat). {
          clear - Hbranch.
          do 37 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 176 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 37) with 37 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JGE_IMM *)
      eapply correct_statement_switch with (n:= 53).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 53%nat). {
          clear - Hbranch.
          do 53 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 160 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 53) with 53 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JLT_IMM *)
      eapply correct_statement_switch with (n:= 165).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 165%nat). {
          clear - Hbranch.
          do 165 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 48 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 165) with 165 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JLE_IMM *)
      eapply correct_statement_switch with (n:= 181).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 181%nat). {
          clear - Hbranch.
          do 181 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 32 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 181) with 181 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSET_IMM *)
      eapply correct_statement_switch with (n:= 69).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 69%nat). {
          clear - Hbranch.
          do 69 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 144 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 69) with 69 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JNE_IMM *)
      eapply correct_statement_switch with (n:= 85).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 85%nat). {
          clear - Hbranch.
          do 85 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 128 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 85) with 85 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSGT_IMM *)
      eapply correct_statement_switch with (n:= 101).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 101%nat). {
          clear - Hbranch.
          do 101 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 112 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 101) with 101 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSGE_IMM *)
      eapply correct_statement_switch with (n:= 117).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 117%nat). {
          clear - Hbranch.
          do 117 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 96 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 117) with 117 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSLT_IMM *)
      eapply correct_statement_switch with (n:= 197).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 197%nat). {
          clear - Hbranch.
          do 197 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 16 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 197) with 197 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSLE_IMM *)
      eapply correct_statement_switch with (n:= 213).
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
        get_invariant _pc.
        get_invariant _len.
        get_invariant _ofs.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1, p2.
        reflexivity.
        intros; simpl.
        unfold eval_inv in *.
        unfold opcode_correct in c3.
        unfold correct_bpf_verifier_get_offset.match_res in c5.
        split; [| tauto].
        intuition congruence.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_well_jump.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x0; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 213%nat). {
          clear - Hbranch.
          do 213 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 213) with 213 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r CALL_IMM *)
      eapply correct_statement_switch with (n:= 133).
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
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_dst_R0.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 133%nat). {
          clear - Hbranch.
          do 133 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 80 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 133) with 133 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RET_IMM *)
      eapply correct_statement_switch with (n:= 149).
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
        exists v.
        unfold exec_expr.
        rewrite p0.
        unfold eval_inv, match_res.
        unfold eval_inv, correct_is_dst_R0.match_res in c3.
        unfold bool_correct in *.
        rewrite c3.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        destruct x; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
        intros.
        constructor.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_imm in Hbranch.
        assert (Hc_eq: c1 = 149%nat). {
          clear - Hbranch.
          do 149 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 64 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 149) with 149 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JMP_IMM_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold eval_inv, opcode_correct in c3.
        destruct c3 as (c3 & Hc3_range).
        exists (Z.of_nat c1).
        split.
        unfold exec_expr.
        rewrite p0.
        rewrite <- c3.
        reflexivity.
        split.

        change Int.modulus with 4294967296.
        change Int.max_unsigned with 4294967295 in Hc3_range.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        unfold nat_to_opcode_branch_imm in Hbranch.
        apply bpf_verifier_opcode_branch_imm_match in Hbranch.
        destruct Hbranch as (Hfirst & Hbranch). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Hbranch; rewrite Hbranch; clear Hbranch.
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

End Bpf_verifier_opcode_branch_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_branch_imm.
