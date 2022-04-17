From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.


(**
Check bpf_verifier_opcode_store_imm.
bpf_verifier_opcode_store_imm
     : nat -> int64 -> M state.state bool
*)
Open Scope Z_scope.

Lemma bpf_verifier_opcode_store_imm_match:
  forall c
  (Hstore : match c with
   | 98%nat => STW
   | 106%nat => STH
   | 114%nat => STB
   | 122%nat => STDW
   | _ => ST_ILLEGAL_INS
   end = ST_ILLEGAL_INS),
      98  <> (Z.of_nat c) /\
      106 <> (Z.of_nat c) /\
      114 <> (Z.of_nat c) /\
      122 <> (Z.of_nat c).
Proof.
  intros.
  do 123 (destruct c; [inversion Hstore; split_conj | ]).
  change 98  with (Z.of_nat 98%nat).
  change 106 with (Z.of_nat 106%nat).
  change 114 with (Z.of_nat 114%nat).
  change 122 with (Z.of_nat 122%nat).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.


Section Bpf_verifier_opcode_store_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_store_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_store_imm.

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

  Instance correct_function_bpf_verifier_opcode_store_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_store_imm.
    simpl.
    unfold INV.
    destruct nat_to_opcode_store_imm eqn: Hstore.
    - (**r STW *)
      eapply correct_statement_switch with (n:= 98).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 98%nat). {
          clear - Hstore.
          do 98 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 24 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 98) with 98 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STH *)
      eapply correct_statement_switch with (n:= 106).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 106%nat). {
          clear - Hstore.
          do 106 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 106) with 106 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STB *)
      eapply correct_statement_switch with (n:= 114).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 114%nat). {
          clear - Hstore.
          do 114 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          do 8 (destruct c; [inversion Hstore|]).
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 114) with 114 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r STDW *)
      eapply correct_statement_switch with (n:= 122).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        eapply correct_body_Sreturn_Some.
        intros.
        exists (Vint (Int.repr 1)).
        unfold exec_expr.
        split; [reflexivity|].
        unfold eval_inv, match_res, bool_correct, Int.one.
        split; [reflexivity|].
        split. unfold Cop.sem_cast; simpl.
        fold Int.one; rewrite Int_eq_one_zero; reflexivity.
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_store_imm in Hstore.
        assert (Hc_eq: c = 122%nat). {
          clear - Hstore.
          do 122 (destruct c; [inversion Hstore|]).
          destruct c; [reflexivity|].
          inversion Hstore.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 122) with 122 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ST_ILLEGAL_INS *)
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
        rewrite <- c1.
        reflexivity.
        split.

        change Int.modulus with 4294967296.
        change Int.max_unsigned with 4294967295 in Hc1_range.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        unfold nat_to_opcode_store_imm in Hstore.
        apply bpf_verifier_opcode_store_imm_match in Hstore.
        destruct Hstore as (Hfirst & Hstore). eapply Coqlib.zeq_false in Hfirst. rewrite Hfirst; clear Hfirst.
        repeat match goal with
        | H: ?X <> ?Y /\ _ |- context[Coqlib.zeq ?X ?Y] =>
            destruct H as (Hfirst & H);
            eapply Coqlib.zeq_false in Hfirst; rewrite Hfirst; clear Hfirst
        end.
        eapply Coqlib.zeq_false in Hstore; rewrite Hstore; clear Hstore.
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

End Bpf_verifier_opcode_store_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_store_imm.
