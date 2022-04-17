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
Check bpf_verifier_opcode_alu64_reg.
bpf_verifier_opcode_alu64_reg
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Lemma bpf_verifier_opcode_alu64_reg_match:
  forall c
  (Halu : match c with
       | 15%nat => ADD64_REG
       | 31%nat => SUB64_REG
       | 47%nat => MUL64_REG
       | 63%nat => DIV64_REG
       | 79%nat => OR64_REG
       | 95%nat => AND64_REG
       | 111%nat => LSH64_REG
       | 127%nat => RSH64_REG
       | 159%nat => MOD64_REG
       | 175%nat => XOR64_REG
       | 191%nat => MOV64_REG
       | 207%nat => ARSH64_REG
       | _ => ALU64_REG_ILLEGAL
       end = ALU64_REG_ILLEGAL),
      15  <> (Z.of_nat c) /\
      31  <> (Z.of_nat c) /\
      47  <> (Z.of_nat c) /\
      63  <> (Z.of_nat c) /\
      79  <> (Z.of_nat c) /\
      95  <> (Z.of_nat c) /\
      111 <> (Z.of_nat c) /\
      127 <> (Z.of_nat c) /\
      159 <> (Z.of_nat c) /\
      175 <> (Z.of_nat c) /\
      191 <> (Z.of_nat c) /\
      207 <> (Z.of_nat c).
Proof.
  intros.
  do 208 (destruct c; [inversion Halu; split_conj | ]).
  change 15  with (Z.of_nat 15%nat).
  change 31  with (Z.of_nat 31%nat).
  change 47  with (Z.of_nat 47%nat).
  change 63  with (Z.of_nat 63%nat).
  change 79  with (Z.of_nat 79%nat).
  change 95  with (Z.of_nat 95%nat).
  change 111 with (Z.of_nat 111%nat).
  change 127 with (Z.of_nat 127%nat).
  change 159 with (Z.of_nat 159%nat).
  change 175 with (Z.of_nat 175%nat).
  change 191 with (Z.of_nat 191%nat).
  change 207 with (Z.of_nat 207%nat).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.

Section Bpf_verifier_opcode_alu64_reg.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_alu64_reg.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_alu64_reg.

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

  Instance correct_function_bpf_verifier_opcode_alu64_reg : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_alu64_reg.
    simpl. (*
    unfold nat_to_opcode_alu64_reg. *)
    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD32 => bindM (upd_reg ... *)
    unfold INV.
    destruct nat_to_opcode_alu64_reg eqn: Halu. (**r case discussion on each alu64_instruction *)
    - (**r ADD64_REG *)
      eapply correct_statement_switch with (n:= 15).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 15%nat). {
          clear - Halu.
          do 15 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 192 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 15) with 15 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r SUB64_REG *)
      eapply correct_statement_switch with (n:= 31).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 31%nat). {
          clear - Halu.
          do 31 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 176 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 31) with 31 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MUL64_REG *)
      eapply correct_statement_switch with (n:= 47).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 47%nat). {
          clear - Halu.
          do 47 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 160 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 47) with 47 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r DIV64_REG *)
      eapply correct_statement_switch with (n:= 63).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 63%nat). {
          clear - Halu.
          do 63 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 144 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 63) with 63 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r OR64_REG *)
      eapply correct_statement_switch with (n:= 79).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 79%nat). {
          clear - Halu.
          do 79 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 128 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 79) with 79 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r AND64_REG *)
      eapply correct_statement_switch with (n:= 95).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 95%nat). {
          clear - Halu.
          do 95 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 112 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 95) with 95 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LSH64_REG *)
      eapply correct_statement_switch with (n:= 111).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 111%nat). {
          clear - Halu.
          do 111 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 96 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 111) with 111 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RSH64_REG *)
      eapply correct_statement_switch with (n:= 127).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 127%nat). {
          clear - Halu.
          do 127 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 80 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 127) with 127 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOD64_REG *)
      eapply correct_statement_switch with (n:= 159).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 159%nat). {
          clear - Halu.
          do 159 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 48 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 159) with 159 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r XOR64_REG *)
      eapply correct_statement_switch with (n:= 175).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 175%nat). {
          clear - Halu.
          do 175 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 32 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 175) with 175 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOV64_REG *)
      eapply correct_statement_switch with (n:= 191).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 191%nat). {
          clear - Halu.
          do 191 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 191) with 191 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ARSH64_REG *)
      eapply correct_statement_switch with (n:= 207).
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
        unfold nat_to_opcode_alu64_reg in Halu.
        assert (Hc_eq: c = 207%nat). {
          clear - Halu.
          do 207 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 207) with 207 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ALU64_REG_ILLEGAL *)
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
        unfold nat_to_opcode_alu64_reg in Halu.
        apply bpf_verifier_opcode_alu64_reg_match in Halu.
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

End Bpf_verifier_opcode_alu64_reg.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_alu64_reg.
