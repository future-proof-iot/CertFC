From bpf.comm Require Import Regs State Monad LemmaNat.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_opcode_mem_ld_reg correct_check_mem correct_cmp_ptr32_nullM correct_upd_flag correct_load_mem correct_upd_reg.


(**
Check step_opcode_mem_ld_reg.

step_opcode_mem_ld_reg
     : val -> int -> reg -> nat -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_mem_ld_reg.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (int:Type); (reg:Type); (nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := step_opcode_mem_ld_reg.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Definition modifies : list block := [state_block]. (* of the C code *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_mem_ld_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
  (DList.DCons (stateM_correct state_block mrs_block ins_block)
    (DList.DCons (stateless val32_correct)
      (DList.DCons (stateless int32_correct)
        (DList.DCons (stateless reg_correct)
          (DList.DCons (stateless opcode_correct)
                (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef.

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

  Instance correct_function3_step_opcode_mem_ld_reg : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app, step_opcode_mem_ld_reg.
    simpl.
    correct_forward correct_statement_seq_body_nil.
    my_reflex.
    reflexivity.
    reflexivity.
    typeclasses eauto.

    { unfold INV.
      unfold var_inv_preserve.
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
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    tauto.

    intros.
    destruct x eqn: HLD.
    - (**r op_BPF_LDXW *)
      eapply correct_statement_switch with (n:= 97%Z).
      + simpl.

        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
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
        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 1)::Vint (Int.repr 4)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        unfold stateless in c4.
        eauto.

        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
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
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_flag.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition congruence.

          revert H6. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3).
        split; auto.
        reflexivity.

        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 4)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        instantiate (1:=ins_block).
        instantiate (1:=mrs_block).
        instantiate (1:=state_block).
        split; [intuition|].
        split; [reflexivity|].
        destruct c4 as (Hv0_eq & Hptr).
        unfold correct_cmp_ptr32_nullM.match_res in c5.
        intuition congruence.

        intros.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_reg.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          inversion H12; subst; clear H12.
          repeat constructor;auto.

          revert H4. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_load_mem.match_res in H1.
          unfold correct_load_mem.match_res.
          unfold correct_upd_reg.match_res in H0.
          intuition eauto.

          revert H5. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition eauto.

          revert H7. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct.
          unfold stateM_correct in H1.
          intuition eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _v.
        exists (v::v0::v1::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split; [reflexivity |].
        intros; simpl.
        unfold correct_load_mem.match_res in c5.
        intuition eauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.

        reflexivity.

        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.

    - (**r op_BPF_LDXH *)
      eapply correct_statement_switch with (n:= 105%Z).
      + simpl.

        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 1)::Vint (Int.repr 2)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        unfold stateless in c4.
        eauto.

        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
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
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_flag.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition congruence.

          revert H6. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.

        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 2)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        instantiate (1:=ins_block).
        instantiate (1:=mrs_block).
        instantiate (1:=state_block).
        split; [intuition|].
        split; [reflexivity|].
        destruct c4 as (Hv0_eq & Hptr).
        unfold correct_cmp_ptr32_nullM.match_res in c5.
        intuition congruence.

        intros.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_reg.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          inversion H12; subst; clear H12.
          repeat constructor;auto.

          revert H4. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_load_mem.match_res in H1.
          unfold correct_load_mem.match_res.
          unfold correct_upd_reg.match_res in H0.
          intuition eauto.

          revert H5. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition eauto.

          revert H7. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct.
          unfold stateM_correct in H1.
          intuition eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _v.
        exists (v::v0::v1::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split; [reflexivity |].
        intros; simpl.
        unfold correct_load_mem.match_res in c5.
        intuition eauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.

        reflexivity.

        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.

    - (**r op_BPF_LDXB *)
      eapply correct_statement_switch with (n:= 113%Z).
      + simpl.

        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 1)::Vint (Int.repr 1)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        unfold stateless in c4.
        eauto.

        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
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
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_flag.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition congruence.

          revert H6. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.

        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 1)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        instantiate (1:=ins_block).
        instantiate (1:=mrs_block).
        instantiate (1:=state_block).
        split; [intuition|].
        split; [reflexivity|].
        destruct c4 as (Hv0_eq & Hptr).
        unfold correct_cmp_ptr32_nullM.match_res in c5.
        intuition congruence.

        intros.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_reg.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          inversion H12; subst; clear H12.
          repeat constructor;auto.

          revert H4. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_load_mem.match_res in H1.
          unfold correct_load_mem.match_res.
          unfold correct_upd_reg.match_res in H0.
          intuition eauto.

          revert H5. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition eauto.

          revert H7. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct.
          unfold stateM_correct in H1.
          intuition eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _v.
        exists (v::v0::v1::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split; [reflexivity |].
        intros; simpl.
        unfold correct_load_mem.match_res in c5.
        intuition eauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.

        reflexivity.

        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.

    - (**r op_BPF_LDXDW *)
      eapply correct_statement_switch with (n:= 121%Z).
      + simpl.

        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
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
        get_invariant _st.
        get_invariant _addr.
        exists (v::Vint (Int.repr 1)::Vint (Int.repr 8)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        unfold stateless in c4.
        eauto.

        intros.
        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
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
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_flag.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          repeat constructor;auto.

          revert H3. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition congruence.

          revert H6. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H0.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 2))::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation, typeof; simpl.
        split; [reflexivity |].
        intros; simpl.
        unfold stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.

        correct_forward correct_statement_seq_body_nil.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.

        { unfold INV.
          unfold var_inv_preserve.
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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 8)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold correct_check_mem.match_res, val_ptr_correct in c4.
        instantiate (1:=ins_block).
        instantiate (1:=mrs_block).
        instantiate (1:=state_block).
        split; [intuition|].
        split; [reflexivity|].
        destruct c4 as (Hv0_eq & Hptr).
        unfold correct_cmp_ptr32_nullM.match_res in c5.
        intuition congruence.

        intros.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        { unfold modifies.
          instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_reg.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          inversion H12; subst; clear H12.
          repeat constructor;auto.

          revert H4. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_load_mem.match_res in H1.
          unfold correct_load_mem.match_res.
          unfold correct_upd_reg.match_res in H0.
          intuition eauto.

          revert H5. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_check_mem.match_res, val_ptr_correct in H1.
          unfold correct_check_mem.match_res, val_ptr_correct.
          intuition eauto.

          revert H7. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_reg.match_res in H0.
          unfold stateM_correct.
          unfold stateM_correct in H1.
          intuition eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _v.
        exists (v::v0::v1::nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split; [reflexivity |].
        intros; simpl.
        unfold correct_load_mem.match_res in c5.
        intuition eauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.

        reflexivity.

        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.
    - (**r op_BPF_LDX_REG_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          correct_get_opcode_mem_ld_reg.match_res op_BPF_LDX_REG_ILLEGAL_INS n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat i)) /\
          (i <> 0x61 /\ i <> 0x69 /\ i <> 0x71 /\ i <> 0x79)%nat /\
          (i <= 255)%nat /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_ld Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat i)))).
        {
          get_invariant _opcode_ld.
          unfold correct_get_opcode_mem_ld_reg.match_res in c3.
          exists v.
          assert (c3':=c3).
          unfold opcode_mem_ld_reg_correct in c3'.
          destruct c3' as (i & V & ILL & RANGE).
          exists i.
          split ; auto.
          split ; auto.
          split ; auto.
          split ; auto.
          unfold exec_expr. congruence.
        }
        destruct Hillegal_ins as (n & i & Hprop & Hn_eq & Hill & Hrange & EX).
        exists (Z.of_nat i).
        split; auto.
        split.

        change Int.modulus with 4294967296.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        repeat destruct Coqlib.zeq; try lia.
        (* default *)
        simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        change (upd_flag Flag.BPF_ILLEGAL_INSTRUCTION) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_INSTRUCTION) (fun _ : unit => returnM tt)).
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. tauto.
        { unfold modifies.
          instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_upd_flag.match_res in H1.
          inversion H2; subst; clear H2.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          repeat constructor;auto.

          revert H4. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold correct_upd_flag.match_res in H1.
          unfold stateM_correct in H2.
          unfold stateM_correct.
          intuition eauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro HH.
        correct_Forall.
        get_invariant _st.
        exists (v ::
                (Vint (Int.neg (Int.repr 1))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split.
        reflexivity.
        intros.
        unfold stateless, flag_correct, CommonLib.int_of_flag; simpl.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        destruct c3 as (_ & c3); split; auto.
        reflexivity.
Qed.

End Step_opcode_mem_ld_reg.

Close Scope Z_scope.

Existing Instance correct_function3_step_opcode_mem_ld_reg.
