From bpf.comm Require Import Regs State Monad LemmaNat.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_opcode_mem_st_imm correct_check_mem correct_cmp_ptr32_nullM correct_upd_flag correct_store_mem_imm.


(**
Check step_opcode_mem_st_imm.
step_opcode_mem_st_imm
     : val -> val -> int -> reg -> nat -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_mem_st_imm.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (val:Type); (int:Type); (reg:Type); (nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := step_opcode_mem_st_imm.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Variable modifies : block. (* of the C code *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_mem_st_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
  (DList.DCons (stateM_correct state_block mrs_block ins_block)
    (DList.DCons (stateless val32_correct)
      (DList.DCons (stateless val32_correct)
        (DList.DCons (stateless int32_correct)
          (DList.DCons (stateless reg_correct)
            (DList.DCons (stateless opcode_correct)
                  (DList.DNil _))))))).

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

  Instance correct_function3_step_opcode_mem_st_imm : forall a, correct_function3 p args res f fn [state_block; modifies] false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app, step_opcode_mem_st_imm.
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
    eauto.

    intros.
    destruct x eqn: HST.
    - (**r op_BPF_STW *)
      eapply correct_statement_switch with (n:= 98%Z).
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
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 4)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        unfold stateless in c5.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        intuition eauto.

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
        unfold correct_check_mem.match_res, val_ptr_correct in c5.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        intros.
        eapply correct_function_modifies_more with (mods' := [state_block]).
        revert a.
        typeclasses eauto.
        unfold incl.
        intros.
        unfold In in *.
        intuition.
        unfold correct_upd_flag.match_res. intuition.
        { instantiate (1:= ins_block).
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
          inversion H12; subst; clear H12.
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
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        instantiate (3:= false).
        instantiate (2:= (DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (val_ptr_correct state_block mrs_block ins_block)
         (DList.DCons (stateless match_chunk)
            (DList.DCons (stateless val32_correct)
              (DList.DNil _)))))).
        instantiate (1:= (fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef)).
        admit.
        admit.
        admit.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 4) :: v1 :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold correct_check_mem.match_res in c5.
        unfold stateless in c6.
        unfold stateless,flag_correct, match_chunk.
        intuition.
        intros.

        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        reflexivity.
        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold correct_get_opcode_mem_st_imm.match_res, opcode_mem_st_imm_correct in c4.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.

    - (**r op_BPF_STH *)
      eapply correct_statement_switch with (n:= 106%Z).
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
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 2)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        unfold stateless in c5.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        intuition eauto.

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
        unfold correct_check_mem.match_res, val_ptr_correct in c5.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        intros.
        eapply correct_function_modifies_more with (mods' := [state_block]).
        revert a.
        typeclasses eauto.
        unfold incl.
        intros.
        unfold In in *.
        intuition.
        unfold correct_upd_flag.match_res. intuition.
        { instantiate (1:= ins_block).
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
          inversion H12; subst; clear H12.
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
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        instantiate (3:= false).
        instantiate (2:= (DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (val_ptr_correct state_block mrs_block ins_block)
         (DList.DCons (stateless match_chunk)
            (DList.DCons (stateless val32_correct)
              (DList.DNil _)))))).
        instantiate (1:= (fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef)).
        admit.
        admit.
        admit.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 2) :: v1 :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold correct_check_mem.match_res in c5.
        unfold stateless in c6.
        unfold stateless,flag_correct, match_chunk.
        intuition.
        intros.

        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        reflexivity.
        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold correct_get_opcode_mem_st_imm.match_res, opcode_mem_st_imm_correct in c4.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.

    - (**r op_BPF_STB *)
      eapply correct_statement_switch with (n:= 114%Z).
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
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 1)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        unfold stateless in c5.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        intuition eauto.

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
        unfold correct_check_mem.match_res, val_ptr_correct in c5.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        intros.
        eapply correct_function_modifies_more with (mods' := [state_block]).
        revert a.
        typeclasses eauto.
        unfold incl.
        intros.
        unfold In in *.
        intuition.
        unfold correct_upd_flag.match_res. intuition.
        { instantiate (1:= ins_block).
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
          inversion H12; subst; clear H12.
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
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        instantiate (3:= false).
        instantiate (2:= (DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (val_ptr_correct state_block mrs_block ins_block)
         (DList.DCons (stateless match_chunk)
            (DList.DCons (stateless val32_correct)
              (DList.DNil _)))))).
        instantiate (1:= (fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef)).
        admit.
        admit.
        admit.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 1) :: v1 :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold correct_check_mem.match_res in c5.
        unfold stateless in c6.
        unfold stateless,flag_correct, match_chunk.
        intuition.
        intros.

        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        reflexivity.
        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold correct_get_opcode_mem_st_imm.match_res, opcode_mem_st_imm_correct in c4.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.


    - (**r op_BPF_STDW *)
      eapply correct_statement_switch with (n:= 122%Z).
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
        exists (v::Vint (Int.repr 2):: Vint (Int.repr 8)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1; reflexivity.
        intros; simpl.
        unfold stateless in c5.
        unfold stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        intuition eauto.

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
        unfold correct_check_mem.match_res, val_ptr_correct in c5.
        intuition eauto.

        intros.
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_MEM) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_MEM) (fun _ : unit => returnM tt)).
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        intros.
        eapply correct_function_modifies_more with (mods' := [state_block]).
        revert a.
        typeclasses eauto.
        unfold incl.
        intros.
        unfold In in *.
        intuition.
        unfold correct_upd_flag.match_res. intuition.
        { instantiate (1:= ins_block).
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
          inversion H12; subst; clear H12.
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
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        instantiate (3:= false).
        instantiate (2:= (DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (val_ptr_correct state_block mrs_block ins_block)
         (DList.DCons (stateless match_chunk)
            (DList.DCons (stateless val32_correct)
              (DList.DNil _)))))).
        instantiate (1:= (fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef)).
        admit.
        admit.
        admit.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _imm.
        exists (v :: v0 :: Vint (Int.repr 8) :: v1 :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold correct_check_mem.match_res in c5.
        unfold stateless in c6.
        unfold stateless,flag_correct, match_chunk.
        intuition.
        intros.

        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.

        reflexivity.
        intros.
        get_invariant _is_null.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_st.
        unfold correct_get_opcode_mem_st_imm.match_res, opcode_mem_st_imm_correct in c4.
        subst.
        unfold exec_expr.
        rewrite p0.
        reflexivity.
      + change Int.modulus with 4294967296.
        lia.

    - (**r op_BPF_ST_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          correct_get_opcode_mem_st_imm.match_res op_BPF_ST_ILLEGAL_INS n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat i)) /\
          (i <> 0x62 /\ i <> 0x6a /\ i <> 0x72 /\ i <> 0x7a)%nat /\
          (i <= 255)%nat /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_st Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat i)))).
        {
          get_invariant _opcode_st.
          unfold correct_get_opcode_mem_st_imm.match_res in c3.
          exists v.
          assert (c4':=c4).
          unfold opcode_mem_st_imm_correct in c4'.
          destruct c4' as (i & V & ILL & RANGE).
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
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        intros.
        eapply correct_function_modifies_more with (mods' := [state_block]).
        revert a.
        typeclasses eauto.
        unfold incl.
        intros.
        unfold In in *.
        intuition.
        unfold correct_upd_flag.match_res. intuition.
        { instantiate (1:= ins_block).
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
          inversion H11; subst; clear H11.
          repeat constructor;auto.

          revert H4. (**r moves the hypotheses  to the goal *)
          unfold match_elt,fst.
          destruct (Maps.PTree.get _ _); try congruence.
          unfold snd.
          intro HH ; destruct HH ; split; auto.
          unfold stateM_correct in *.
          tauto.
        }
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        rename H into Htmp.
        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        exists (v::Vint (Int.neg (Int.repr 1))::nil). (**r star here *)
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
        unfold stateM_correct in c4.
        destruct c4 as (_ & c4); auto.
        reflexivity.
Admitted.

End Step_opcode_mem_st_imm.

Close Scope Z_scope.

Existing Instance correct_function3_step_opcode_mem_st_imm.
