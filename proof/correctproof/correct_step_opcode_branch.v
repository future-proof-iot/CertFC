From bpf.comm Require Import Regs State Monad.
From bpf.src Require Import DxNat DxIntegers DxValues DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.proof.correctproof Require Import correct_get_opcode_branch correct_upd_pc
correct_upd_flag.

(**
Check step_opcode_branch.
step_opcode_branch
     : val64_t ->
       val64_t -> DxIntegers.sint32_t -> DxIntegers.sint32_t -> nat8 -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_branch.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val64_t:Type); (val64_t:Type); (sint32_t:Type); (sint32_t:Type); (nat8:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := step_opcode_branch.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_branch.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons stateM_correct
      (DList.DCons (stateless val64_correct)
       (DList.DCons (stateless val64_correct)
          (DList.DCons (stateless sint32_correct)
          (DList.DCons (stateless sint32_correct)
            (DList.DCons (stateless opcode_alu64_nat8_correct)
                    (DList.DNil _))))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_state state_block mrs_block ins_block st m.


Ltac build_app_aux T :=
  match T with
  | ?F ?X => let ty := type of X in
             let r := build_app_aux F in
             constr:((mk ty X) :: r)
  | ?X    => constr:(@nil dpair)
  end.                                    

Ltac get_function T :=
  match T with
  | ?F ?X => get_function F
  | ?X    => X
  end.

Ltac build_app T :=
  let a := build_app_aux T in
  let v := (eval simpl in (DList.of_list_dp (List.rev a))) in
  let f := get_function T in
  match type of v with
  | DList.t _ ?L =>
      change T with (app (f: arrow_type L _) v)
  end.

Ltac change_app_for_body :=
  match goal with
  | |- @correct_body _ _ ?F _ _ _ _ _ _ _ _
    => build_app F
  end.

Ltac change_app_for_statement :=
  match goal with
  | |- @correct_statement _ _ ?F _ _ _ _ _ _ _ _
    => build_app F
  end.

Ltac prove_incl :=
  simpl; unfold incl; simpl; intuition congruence.

Ltac prove_in_inv :=
  simpl; intuition subst; discriminate.

Ltac correct_forward L :=
  match goal with
  | |- @correct_body _ _ (bindM ?F1 ?F2)  _
                     (Ssequence
                        (Ssequence
                           (Scall _ _ _)
                           (Sset ?V ?T))
                        ?R)
                     _ _ _ _ _ _  =>
      eapply L;
      [ change_app_for_statement ;
        let b := match T with
                 | Ecast _ _ => constr:(true)
                 | _         => constr:(false)
                 end in
        eapply correct_statement_call with (has_cast := b)
      |]
  | |- @correct_body _ _ (match  ?x with true => _ | false => _ end) _
                     (Sifthenelse _ _ _)
                     _ _ _ _ _ _  =>
      eapply correct_statement_if_body; [prove_in_inv | destruct x ]
  end.

  Lemma Cop_add : forall vl1 vl2 m,
       Cop.sem_binary_operation (globalenv p) Cop.Oadd
                                (Vlong vl1) Clightdefs.tulong (Vlong vl2) Clightdefs.tulong m =
         Some (Vlong (Int64.add vl1 vl2)).
  Proof.
    reflexivity.
  Qed.

  Instance correct_function3_step_opcode_branch : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, step_opcode_branch.
    simpl.
    (** goal: correct_body _ _ (bindM (get_opcode_branch _) ... *)
    correct_forward correct_statement_seq_body_nil.

    my_reflex.
    my_reflex.
    reflexivity.
    typeclasses eauto.

    { unfold INV.
      unfold var_inv_preserve. (**r unmodifies_effect is not enough, we also need unmodifies_effect_state *)
      intros.
      unfold match_temp_env in *.
      rewrite Forall_fold_right in *.
      simpl in *.
      destruct H; subst.
      intuition.
    }

    reflexivity.
    reflexivity.
    reflexivity.
    prove_in_inv.
    prove_in_inv.
    reflexivity.
    reflexivity.

    unfold INV; intro H.
    correct_Forall.
    get_invariant _op.
    exists (v::nil).
    split.
    unfold map_opt. unfold exec_expr. rewrite p0.
    reflexivity.
    intros. simpl.
    tauto.

    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD64 => bindM (upd_reg ... *)
    intros.
    unfold INV.
    destruct x eqn: Hbranch. (**r case discussion on each branch_instruction *)
    - (**r op_BPF_JA *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold nat8_0x05.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (c3 =? 5)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        destruct c4 as (c4_1 & c4_2).
        exists (v ::Vint (Int.repr (-1)) :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,flag_correct.
        unfold int_of_flag; simpl. reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_alu64_nat8_correct in c4.
        destruct c4 as ((Hv_eq & Hland & Hrange) & Hc4).
        rewrite <- Hv_eq.
        destruct (c3 =? 5)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c3)) (Int.repr 5) = false). {
          apply Int.eq_false.
          apply nat8_neq_5; auto.
        }
        rewrite Hneq; clear Hneq.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.

    - (**r op_BPF_JEQ *)
      eapply correct_statement_switch with (n:= 0x10).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_eq.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 => match c0 with
                  | Vlong n2 => Int64.eq n1 n2
                  | _ => false
                  end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JGT *)
      eapply correct_statement_switch with (n:= 0x20).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_gt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 => match c0 with
                  | Vlong n2 => Int64.ltu n2 n1
                  | _ => false
                  end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JGE *)
      eapply correct_statement_switch with (n:= 0x30).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_ge.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 =>
        match c0 with
        | Vlong n2 => negb (Int64.ltu n1 n2)
        | _ => false
        end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JLT *)
      eapply correct_statement_switch with (n:= 0xa0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_lt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 => match c0 with
                  | Vlong n2 => Int64.ltu n1 n2
                  | _ => false
                  end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JLE *)
      eapply correct_statement_switch with (n:= 0xb0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_le.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 =>
        match c0 with
        | Vlong n2 => negb (Int64.ltu n2 n1)
        | _ => false
        end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JSET *)
      eapply correct_statement_switch with (n:= 0x40).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_set.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 =>
        match c0 with
        | Vlong n2 => negb (Int64.eq (Int64.and n1 n2) Int64.zero)
        | _ => false
        end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JNE *)
      eapply correct_statement_switch with (n:= 0x50).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_ne.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 =>
        match c0 with
        | Vlong n2 => negb (Int64.eq n1 n2)
        | _ => false
        end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JSGT *)
      eapply correct_statement_switch with (n:= 0x60).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_gt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 => match c0 with
                  | Vlong n2 => Int64.lt n2 n1
                  | _ => false
                  end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JSGE *)
      eapply correct_statement_switch with (n:= 0x70).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_ge.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 =>
        match c0 with
        | Vlong n2 => negb (Int64.lt n1 n2)
        | _ => false
        end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JSLT *)
      eapply correct_statement_switch with (n:= 0xc0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_lt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 => match c0 with
                  | Vlong n2 => Int64.lt n1 n2
                  | _ => false
                  end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_JSLE *)
      eapply correct_statement_switch with (n:= 0xd0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_le.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr.

        destruct (match c with
    | Vlong n1 =>
        match c0 with
        | Vlong n2 => negb (Int64.lt n2 n1)
        | _ => false
        end
    | _ => false
    end)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_pc.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_pc.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        rewrite p1. rewrite p2.
        split.
        subst.
        Transparent Archi.ptr64.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,sint32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        destruct c4 as (c4 & _); unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        destruct c5 as (c5 & _); unfold stateless, val64_correct in c5.
        destruct c5 as (c5_eq & (c5_vl & c5)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_RET *)

      eapply correct_statement_switch with (n:= 0x90).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold nat8_0x95.
        (**r because upd_reg return unit, here we use *_unit? *)

        eapply correct_statement_if_body_expr.

        destruct (c3 =? 149)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          destruct H1, H0.
          split; assumption.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.repr 1) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split. reflexivity.
        subst.
        intros.
        simpl.
        intuition.
        unfold stateless,flag_correct, int_of_flag.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        destruct c4 as (c4_1 & c4_2).
        exists (v ::Vint (Int.repr (-1)) :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,flag_correct.
        unfold int_of_flag; simpl. reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_alu64_nat8_correct in c4.
        destruct c4 as ((Hv_eq & Hland & Hrange) & Hc4).
        rewrite <- Hv_eq.
        destruct (c3 =? 149)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c3)) (Int.repr 149) = false). {
          apply Int.eq_false.
          apply nat8_neq_149; auto.
        }
        rewrite Hneq; clear Hneq.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4; assumption.
      + compute. intuition congruence.

    - (**r op_BPF_JMP_ILLEGAL_INS *)
      admit.
(*
      eapply correct_statement_switch with (n:= 1).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          instantiate (1 := mrs_block) in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _st le1); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          destruct H1, H0.
          split; assumption.
          rewrite Forall_forall in H10.
          apply H10.
          unfold In. eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        destruct c4 as (c4_1 & c4_2).
        destruct c5 as (c5_1 & c5_2).
        unfold sint32_correct,stateless in c5_1, c6.
        destruct c6 as (c6_1 & c6_2).
        exists (v :: Vint (Int.repr (-1)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split. reflexivity.
        subst.
        intros.
        simpl.
        intuition.
        unfold stateless,flag_correct, int_of_flag.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        intros.
        get_invariant _st.
        destruct c4 as (c4 & _); unfold stateM_correct in c4.
        destruct c4 as (_ & c4); assumption.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c4.
        unfold opcode_branch_correct in c4.
        (* opcode_branch_correct should be a mapping between opcodes and int *)
        destruct c4. assumption.
      + compute. intuition congruence.*)

Admitted.

End Step_opcode_branch.

Close Scope Z_scope.

Existing Instance correct_function3_step_opcode_branch.
