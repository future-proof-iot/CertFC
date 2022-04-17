From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import LemmaNat Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import opcode_synthesis verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.
From bpf.verifier.simulation Require Import correct_is_not_div_by_zero64 correct_is_shift_range64.


(**
Check bpf_verifier_opcode_alu64_imm.
bpf_verifier_opcode_alu64_imm
     : nat -> int64 -> M bool

*)
Open Scope Z_scope.

Lemma bpf_verifier_opcode_alu64_imm_match:
  forall c
    (Halu : match c with
       | 7%nat => ADD64_IMM
       | 23%nat => SUB64_IMM
       | 39%nat => MUL64_IMM
       | 55%nat => DIV64_IMM
       | 71%nat => OR64_IMM
       | 87%nat => AND64_IMM
       | 103%nat => LSH64_IMM
       | 119%nat => RSH64_IMM
       | 135%nat => NEG64_IMM
       | 151%nat => MOD64_IMM
       | 167%nat => XOR64_IMM
       | 183%nat => MOV64_IMM
       | 199%nat => ARSH64_IMM
       | _ => ALU64_IMM_ILLEGAL
       end = ALU64_IMM_ILLEGAL),
          7   <> (Z.of_nat c) /\
          23  <> (Z.of_nat c) /\
          39  <> (Z.of_nat c) /\
          55  <> (Z.of_nat c) /\
          71  <> (Z.of_nat c) /\
          87  <> (Z.of_nat c) /\
          103 <> (Z.of_nat c) /\
          119 <> (Z.of_nat c) /\
          135 <> (Z.of_nat c) /\
          151 <> (Z.of_nat c) /\
          167 <> (Z.of_nat c) /\
          183 <> (Z.of_nat c) /\
          199 <> (Z.of_nat c).
Proof.
  intros.
  do 200 (destruct c; [inversion Halu; split_conj | ]).
  change 7   with (Z.of_nat 7%nat).
  change 23  with (Z.of_nat 23%nat).
  change 39  with (Z.of_nat 39%nat).
  change 55  with (Z.of_nat 55%nat).
  change 71  with (Z.of_nat 71%nat).
  change 87  with (Z.of_nat 87%nat).
  change 103 with (Z.of_nat 103%nat).
  change 119 with (Z.of_nat 119%nat).
  change 135 with (Z.of_nat 135%nat).
  change 151 with (Z.of_nat 151%nat).
  change 167 with (Z.of_nat 167%nat).
  change 183 with (Z.of_nat 183%nat).
  change 199 with (Z.of_nat 199%nat).
  repeat (split; [intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse |]).
  intro Hfalse; apply Nat2Z.inj in Hfalse; inversion Hfalse.
Qed.



Section Bpf_verifier_opcode_alu64_imm.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := bpf_verifier_opcode_alu64_imm.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_verifier_opcode_alu64_imm.

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

  Instance correct_function_bpf_verifier_opcode_alu64_imm : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, bpf_verifier_opcode_alu64_imm.
    simpl. (*
    unfold nat_to_opcode_alu64_reg. *)
    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD32 => bindM (upd_reg ... *)
    unfold INV.
    destruct nat_to_opcode_alu64_imm eqn: Halu. (**r case discussion on each alu64_instruction *)
    - (**r ADD64_IMM *)
      eapply correct_statement_switch with (n:= 7).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 7%nat). {
          clear - Halu.
          do 7 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 192 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 7) with 7 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r SUB64_IMM *)
      eapply correct_statement_switch with (n:= 23).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 23%nat). {
          clear - Halu.
          do 23 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 176 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 23) with 23 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MUL64_IMM *)
      eapply correct_statement_switch with (n:= 39).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 39%nat). {
          clear - Halu.
          do 39 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 160 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 39) with 39 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r DIV64_IMM *)
      eapply correct_statement_switch with (n:= 55).
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
        unfold eval_inv, correct_is_not_div_by_zero64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 55%nat). {
          clear - Halu.
          do 55 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 144 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 55) with 55 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r OR64_IMM *)
      eapply correct_statement_switch with (n:= 71).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 71%nat). {
          clear - Halu.
          do 71 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 128 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 71) with 71 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r AND64_IMM *)
      eapply correct_statement_switch with (n:= 87).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 87%nat). {
          clear - Halu.
          do 87 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 112 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 87) with 87 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r LSH64_IMM *)
      eapply correct_statement_switch with (n:= 103).
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
        exists (v:: (Vint (Int.repr 64)) ::nil).
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
        unfold eval_inv, correct_is_shift_range64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 103%nat). {
          clear - Halu.
          do 103 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 96 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 103) with 103 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r RSH64_IMM *)
      eapply correct_statement_switch with (n:= 119).
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
        exists (v:: (Vint (Int.repr 64)) ::nil).
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
        unfold eval_inv, correct_is_shift_range64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 119%nat). {
          clear - Halu.
          do 119 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 80 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 119) with 119 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r NEG64_IMM *)
      eapply correct_statement_switch with (n:= 135).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 135%nat). {
          clear - Halu.
          do 135 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 64 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 135) with 135 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOD64_IMM *)
      eapply correct_statement_switch with (n:= 151).
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
        unfold eval_inv, correct_is_not_div_by_zero64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 151%nat). {
          clear - Halu.
          do 151 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 48 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 151) with 151 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r XOR64_IMM *)
      eapply correct_statement_switch with (n:= 167).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 167%nat). {
          clear - Halu.
          do 167 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 32 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 167) with 167 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r MOV64_IMM *)
      eapply correct_statement_switch with (n:= 183).
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 183%nat). {
          clear - Halu.
          do 183 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          do 16 (destruct c; [inversion Halu|]).
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 183) with 183 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ARSH64_IMM *)
      eapply correct_statement_switch with (n:= 199).
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
        exists (v:: (Vint (Int.repr 64)) ::nil).
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
        unfold eval_inv, correct_is_shift_range64.match_res, bool_correct in c1.
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
        unfold nat_to_opcode_alu64_imm in Halu.
        assert (Hc_eq: c = 199%nat). {
          clear - Halu.
          do 199 (destruct c; [inversion Halu|]).
          destruct c; [reflexivity|].
          inversion Halu.
        }
        rewrite Hc_eq in *.
        destruct c1 as (c1 & _).
        change (Z.of_nat 199) with 199 in c1.
        symmetry; assumption.
      + compute. intuition congruence.
    - (**r ALU64_IMM_ILLEGAL *)
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
        unfold nat_to_opcode_alu64_imm in Halu.
        apply bpf_verifier_opcode_alu64_imm_match in Halu.
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

End Bpf_verifier_opcode_alu64_imm.

Close Scope Z_scope.

Existing Instance correct_function_bpf_verifier_opcode_alu64_imm.
