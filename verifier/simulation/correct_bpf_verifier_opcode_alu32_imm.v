From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.
From bpf.verifier.simulation Require Import correct_is_not_div_by_zero correct_is_shift_range.


(**
Check bpf_verifier_opcode_alu32_imm.
bpf_verifier_opcode_alu32_imm
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Lemma bpf_verifier_opcode_alu32_imm_match:
  forall c
    (Halu : match c with
       | 4%nat => ADD32_IMM
       | 20%nat => SUB32_IMM
       | 36%nat => MUL32_IMM
       | 52%nat => DIV32_IMM
       | 68%nat => OR32_IMM
       | 84%nat => AND32_IMM
       | 100%nat => LSH32_IMM
       | 116%nat => RSH32_IMM
       | 132%nat => NEG32_IMM
       | 148%nat => MOD32_IMM
       | 164%nat => XOR32_IMM
       | 180%nat => MOV32_IMM
       | 196%nat => ARSH32_IMM
       | _ => ALU32_IMM_ILLEGAL
       end = ALU32_IMM_ILLEGAL),
          4   <> (Z.of_nat c) /\
          20  <> (Z.of_nat c) /\
          36  <> (Z.of_nat c) /\
          52  <> (Z.of_nat c) /\
          68  <> (Z.of_nat c) /\
          84  <> (Z.of_nat c) /\
          100 <> (Z.of_nat c) /\
          116 <> (Z.of_nat c) /\
          132 <> (Z.of_nat c) /\
          148 <> (Z.of_nat c) /\
          164 <> (Z.of_nat c) /\
          180 <> (Z.of_nat c) /\
          196 <> (Z.of_nat c).
Proof.
  intros.
  do 197 (destruct c; [inversion Halu; split_conj | ]).
  change 4   with (Z.of_nat 4%nat).
  change 20  with (Z.of_nat 20%nat).
  change 36  with (Z.of_nat 36%nat).
  change 52  with (Z.of_nat 52%nat).
  change 68  with (Z.of_nat 68%nat).
  change 84  with (Z.of_nat 84%nat).
  change 100 with (Z.of_nat 100%nat).
  change 116 with (Z.of_nat 116%nat).
  change 132 with (Z.of_nat 132%nat).
  change 148 with (Z.of_nat 148%nat).
  change 164 with (Z.of_nat 164%nat).
  change 180 with (Z.of_nat 180%nat).
  change 196 with (Z.of_nat 196%nat).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.


Section Bpf_verifier_opcode_alu32_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_alu32_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_alu32_imm.

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

  Instance correct_function_bpf_verifier_opcode_alu32_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_alu32_imm.
    simpl. (*
    unfold nat_to_opcode_alu32_reg. *)
    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD32 => bindM (upd_reg ... *)
    unfold INV.
    destruct nat_to_opcode_alu32_imm eqn: Halu. (**r case discussion on each alu32_instruction *)
    - (**r ADD32_IMM *)
      eapply correct_statement_switch with (n:= 4).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 4%nat). {
          clear - Halu.
          do 4 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 192 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 4) with 4 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r SUB32_IMM *)
      eapply correct_statement_switch with (n:= 20).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 20%nat). {
          clear - Halu.
          do 20 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 176 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 20) with 20 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MUL32_IMM *)
      eapply correct_statement_switch with (n:= 36).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 36%nat). {
          clear - Halu.
          do 36 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 160 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 36) with 36 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r DIV32_IMM *)
      eapply correct_statement_switch with (n:= 52).
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
        unfold eval_inv, correct_is_not_div_by_zero.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 52%nat). {
          clear - Halu.
          do 52 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 144 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 52) with 52 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r OR32_IMM *)
      eapply correct_statement_switch with (n:= 68).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 68%nat). {
          clear - Halu.
          do 68 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 128 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 68) with 68 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r AND32_IMM *)
      eapply correct_statement_switch with (n:= 84).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 84%nat). {
          clear - Halu.
          do 84 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 112 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 84) with 84 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LSH32_IMM *)
      eapply correct_statement_switch with (n:= 100).
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
        exists (v:: (Vint (Int.repr 32)) ::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        unfold eval_inv in c1.
        split; [assumption |].
        unfold int32_correct.
        tauto.

        intros.
        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold eval_inv, correct_is_shift_range.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 100%nat). {
          clear - Halu.
          do 100 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 96 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 100) with 100 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RSH32_IMM *)
      eapply correct_statement_switch with (n:= 116).
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
        exists (v:: (Vint (Int.repr 32)) ::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        unfold eval_inv in c1.
        split; [assumption |].
        unfold int32_correct.
        tauto.

        intros.
        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold eval_inv, correct_is_shift_range.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 116%nat). {
          clear - Halu.
          do 116 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 80 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 116) with 116 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r NEG32_IMM *)
      eapply correct_statement_switch with (n:= 132).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 132%nat). {
          clear - Halu.
          do 132 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 64 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 132) with 132 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOD32_IMM *)
      eapply correct_statement_switch with (n:= 148).
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
        unfold eval_inv, correct_is_not_div_by_zero.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 148%nat). {
          clear - Halu.
          do 148 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 48 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 148) with 148 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r XOR32_IMM *)
      eapply correct_statement_switch with (n:= 164).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 164%nat). {
          clear - Halu.
          do 164 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 32 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 164) with 164 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOV32_IMM *)
      eapply correct_statement_switch with (n:= 180).
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
        split; [reflexivity|].
        intros.
        constructor.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 180%nat). {
          clear - Halu.
          do 180 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 180) with 180 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ARSH32_IMM *)
      eapply correct_statement_switch with (n:= 196).
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
        exists (v:: (Vint (Int.repr 32)) ::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0.
        reflexivity.
        intros. simpl.
        unfold eval_inv in c1.
        split; [assumption |].
        unfold int32_correct.
        tauto.

        intros.
        eapply correct_body_Sreturn_Some.
        intros.
        get_invariant _b.
        unfold eval_inv, correct_is_shift_range.match_res, bool_correct in c1.
        exists v.
        unfold exec_expr.
        rewrite p0.
        split; [reflexivity | ].
        unfold eval_inv, match_res, bool_correct.
        rewrite c1.
        split; [reflexivity | ].
        unfold Cop.sem_cast; simpl.
        split; [destruct x; reflexivity | ].
        intros; simpl.
        constructor.
        simpl.
        destruct x; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold eval_inv, opcode_correct in c1.
        unfold nat_to_opcode_alu32_imm in Halu.
        assert (Hc_eq: c = 196%nat). {
          clear - Halu.
          do 196 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 196) with 196 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ALU32_IMM_ILLEGAL *)
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
        unfold nat_to_opcode_alu32_imm in Halu.
        apply bpf_verifier_opcode_alu32_imm_match in Halu.
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

End Bpf_verifier_opcode_alu32_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_alu32_imm.
