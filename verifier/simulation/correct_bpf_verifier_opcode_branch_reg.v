From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.
From bpf.verifier.simulation Require Import correct_bpf_verifier_get_offset correct_is_well_src correct_is_well_jump.


(**
Check bpf_verifier_opcode_branch_reg.
bpf_verifier_opcode_branch_reg
     : nat -> nat -> nat -> int64 -> M bool

*)
Open Scope Z_scope.

Lemma bpf_verifier_opcode_branch_reg_match:
  forall c
    (Hbranch : match c with
      | 29%nat => JEQ_REG
      | 45%nat => JGT_REG
      | 61%nat => JGE_REG
      | 77%nat => JSET_REG
      | 93%nat => JNE_REG
      | 109%nat => JSGT_REG
      | 125%nat => JSGE_REG
      | 173%nat => JLT_REG
      | 189%nat => JLE_REG
      | 205%nat => JSLT_REG
      | 221%nat => JSLE_REG
      | _ => JMP_REG_ILLEGAL_INS
      end = JMP_REG_ILLEGAL_INS),
        29  <> (Z.of_nat c) /\
        45  <> (Z.of_nat c) /\
        61  <> (Z.of_nat c) /\
        77  <> (Z.of_nat c) /\
        93  <> (Z.of_nat c) /\
        109 <> (Z.of_nat c) /\
        125 <> (Z.of_nat c) /\
        173 <> (Z.of_nat c) /\
        189 <> (Z.of_nat c) /\
        205 <> (Z.of_nat c) /\
        221 <> (Z.of_nat c).
Proof.
  intros.
  do 222 (destruct c; [inversion Hbranch; split_conj | ]).
  change 29  with (Z.of_nat 29%nat).
  change 45  with (Z.of_nat 45%nat).
  change 61  with (Z.of_nat 61%nat).
  change 77  with (Z.of_nat 77%nat).
  change 93  with (Z.of_nat 93%nat).
  change 109 with (Z.of_nat 109%nat).
  change 125 with (Z.of_nat 125%nat).
  change 173 with (Z.of_nat 173%nat).
  change 189 with (Z.of_nat 189%nat).
  change 205 with (Z.of_nat 205%nat).
  change 221 with (Z.of_nat 221%nat).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.


Section Bpf_verifier_opcode_branch_reg.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (nat:Type); (nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_branch_reg.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_branch_reg.

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

  Instance correct_function_bpf_verifier_opcode_branch_reg : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_branch_reg.
    simpl.
    unfold INV.
    destruct nat_to_opcode_branch_reg eqn: Hbranch. (**r case discussion on each branch_instruction *)
    - (**r JEQ_REG *)
      eapply correct_statement_switch with (n:= 29).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 29%nat). {
          clear - Hbranch.
          do 29 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 192 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 29) with 29 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JGT_REG *)
      eapply correct_statement_switch with (n:= 45).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 45%nat). {
          clear - Hbranch.
          do 45 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 176 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 45) with 45 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JGE_REG *)
      eapply correct_statement_switch with (n:= 61).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 61%nat). {
          clear - Hbranch.
          do 61 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 160 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 61) with 61 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JLT_REG *)
      eapply correct_statement_switch with (n:= 173).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 173%nat). {
          clear - Hbranch.
          do 173 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 48 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 173) with 173 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JLE_REG *)
      eapply correct_statement_switch with (n:= 189).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 189%nat). {
          clear - Hbranch.
          do 189 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 32 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 189) with 189 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSET_REG *)
      eapply correct_statement_switch with (n:= 77).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 77%nat). {
          clear - Hbranch.
          do 77 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 144 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 77) with 77 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JNE_REG *)
      eapply correct_statement_switch with (n:= 93).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 93%nat). {
          clear - Hbranch.
          do 93 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 128 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 93) with 93 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSGT_REG *)
      eapply correct_statement_switch with (n:= 109).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 109%nat). {
          clear - Hbranch.
          do 109 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 112 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 109) with 109 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSGE_REG *)
      eapply correct_statement_switch with (n:= 125).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 125%nat). {
          clear - Hbranch.
          do 125 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 96 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 125) with 125 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSLT_REG *)
      eapply correct_statement_switch with (n:= 205).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 205%nat). {
          clear - Hbranch.
          do 205 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          do 16 (destruct c1; [inversion Hbranch|]).
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 205) with 205 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JSLE_REG *)
      eapply correct_statement_switch with (n:= 221).
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        tauto.
        intros.

        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x0 eqn: Hx0_eq.
        * eapply correct_statement_seq_body with (modifies1:=ModNothing).
          change_app_for_statement.
          eapply correct_statement_call with (has_cast := true).
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

          intros.
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
          destruct x1; [rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity.
          intros.
          constructor.
          destruct x1; reflexivity.
          reflexivity.
        * eapply correct_body_Sreturn_Some.
          intros.
          exists (Vint (Int.repr 0)).
          unfold exec_expr.
          split; [reflexivity|].
          unfold eval_inv, match_res, bool_correct, Int.zero.
          split; [reflexivity|].
          split. unfold Cop.sem_cast; simpl.
          fold Int.zero.
          rewrite Int.eq_true; reflexivity.
          intros.
          constructor.
          reflexivity.
        * reflexivity.
        * intros.
          get_invariant _b0.
          unfold exec_expr.
          rewrite p0. f_equal.
          unfold eval_inv, correct_is_well_src.match_res, bool_correct in c3.
          unfold nat_to_opcode_branch_reg in Hbranch.
          unfold Val.of_bool, Vtrue, Vfalse.
          rewrite c3. destruct x0; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, nat_correct in c3.
        unfold nat_to_opcode_branch_reg in Hbranch.
        assert (Hc_eq: c1 = 221%nat). {
          clear - Hbranch.
          do 221 (destruct c1; [inversion Hbranch|]).
          destruct c1; [reflexivity|].
          inversion Hbranch.
        }
        rewrite Hc_eq in *.
        destruct c3 as (c3 & _).
        change (Z.of_nat 221) with 221 in c3.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r JMP_REG_ILLEGAL_INS *)
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
        unfold nat_to_opcode_branch_reg in Hbranch.
        apply bpf_verifier_opcode_branch_reg_match in Hbranch.
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

End Bpf_verifier_opcode_branch_reg.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_branch_reg.
