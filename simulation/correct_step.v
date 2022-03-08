From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From bpf.monadicmodel Require Import Opcode.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_eval_pc correct_eval_ins correct_get_opcode_ins correct_get_opcode correct_get_dst correct_eval_reg correct_get_src64 correct_step_opcode_alu64 correct_reg64_to_reg32 correct_get_src32 correct_step_opcode_alu32 correct_get_offset correct_step_opcode_branch correct_get_immediate correct_step_opcode_mem_ld_imm correct_get_addr_ofs correct_step_opcode_mem_ld_reg correct_step_opcode_mem_st_imm correct_step_opcode_mem_st_reg correct_upd_flag.


(**
Check rBPFInterpreter.step.
rBPFInterpreter.step
     : M unit

*)
Open Scope Z_scope.

Section Step.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := rBPFInterpreter.step.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Variable modifies : list block. (* of the C code *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons (stateM_correct state_block mrs_block ins_block)
                    (DList.DNil _)).

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

  Instance correct_function3_step: forall a, correct_function3 p args res f fn (state_block::modifies) false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, rBPFInterpreter.step.
    simpl.
    (** goal: correct_body _ _ (bindM (eval_pc _) ... *)
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
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    intuition eauto.

    intros.
    (** goal: correct_body _ _ (bindM (eval_ins _) ... *)
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
    get_invariant _pc.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
    intros; simpl.
    unfold correct_eval_pc.match_res in c0.
    unfold stateless.
    intuition eauto.

    intros.
    (** goal: correct_body _ _ (bindM (get_opcode_ins _) ... *)
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
    get_invariant _ins.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold correct_eval_ins.match_res in c.
    unfold stateless.
    intuition eauto.

    intros.
    (** goal: correct_body _ _ (bindM (get_opcode _) ... *)
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
    unfold correct_get_opcode_ins.match_res in c.
    unfold stateless.
    intuition eauto.

    intros.
    (** goal: correct_body _ _ (bindM (get_dst _) ... *)
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
    get_invariant _ins.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold correct_eval_ins.match_res in c.
    unfold stateless.
    intuition eauto.

    intros.
    (** goal: correct_body _ _
              match x with
              | op_BPF_ALU64 => bindM (eval_reg ... *)
    unfold INV.
    destruct x2 eqn: Hins.
    - (**r op_BPF_ALU64 *)
      eapply correct_statement_switch with (n:= 7).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
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
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_get_dst.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src64 _) ... *)
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
        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1,p2; reflexivity.
        intros; simpl.
        unfold correct_get_opcode_ins.match_res in c0.
        unfold correct_eval_ins.match_res in c1.
        unfold stateless.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_alu64 x4 x5 x3 x1 =
              bindM (step_opcode_alu64 x4 x5 x3 x1) (fun _ : unit => returnM tt)). {
          clear - st7.
        Ltac val_op :=
          match goal with
          | |- context[match
                   match ?X with
                   | _ => _
                   end
                  with _ => _ end] =>
            destruct X; try reflexivity
          end.
          unfold step_opcode_alu64, get_opcode_alu64.
          unfold bindM, returnM.
          destruct byte_to_opcode_alu64; try reflexivity; unfold upd_reg.
          val_op. val_op.  val_op.
          destruct (rBPFValues.compl_ne _ _); try reflexivity.
          destruct (rBPFValues.val64_divlu _ _); try reflexivity.
          val_op. val_op.
          unfold reg64_to_reg32, returnM.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.shll; try reflexivity.
          unfold reg64_to_reg32, returnM.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.shrlu; try reflexivity.
          destruct (x1 =? 135)%nat; try reflexivity.
          destruct Val.negl; try reflexivity.
          destruct rBPFValues.compl_ne; try reflexivity.
          destruct rBPFValues.val64_modlu; try reflexivity.
          destruct Val.xorl; try reflexivity.
          destruct x5; try reflexivity.
          unfold reg64_to_reg32, returnM.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.shrl; try reflexivity.
        }
        rewrite Heq; clear Heq.
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
        unfold correct_step_opcode_alu64.match_res. intuition.
        { instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_step_opcode_alu64.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          repeat constructor;auto.

          revert H10. (**r moves the hypotheses  to the goal *)
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

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst64.
        get_invariant _src64.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 :: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c0.
        unfold correct_get_src64.match_res in c1.
        unfold correct_get_dst.match_res in c2.
        unfold correct_get_opcode_ins.match_res in c3.
        unfold stateless.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_ALU32 *)
      eapply correct_statement_switch with (n:= 4).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
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
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_get_dst.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (reg64_to_reg32 _) ... *)
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
        get_invariant _dst64.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src32 _) ... *)
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
        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1,p2; reflexivity.
        intros; simpl.
        unfold correct_get_opcode_ins.match_res in c0.
        unfold correct_eval_ins.match_res in c1.
        unfold stateless.
        intuition eauto.

        intros.

        assert (Heq:
              step_opcode_alu32 x5 x6 x3 x1 =
              bindM (step_opcode_alu32 x5 x6 x3 x1) (fun _ : unit => returnM tt)). {
          clear - st7.
          unfold step_opcode_alu32, get_opcode_alu32.
          unfold bindM, returnM.
          destruct byte_to_opcode_alu32; try reflexivity; unfold upd_reg.
          val_op. val_op.  val_op.
          destruct rBPFValues.comp_ne_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct (x1 =? 132)%nat; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.comp_ne_32; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct Val.longofintu; try reflexivity.
          destruct rBPFValues.compu_lt_32; try reflexivity.
          destruct Val.longofint; try reflexivity.
        }
        rewrite Heq; clear Heq.
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
        unfold correct_step_opcode_alu32.match_res. intuition.
        { instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_step_opcode_alu32.match_res in H0.
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

          revert H11. (**r moves the hypotheses  to the goal *)
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

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst32.
        get_invariant _src32.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 :: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c0.
        unfold correct_get_src32.match_res in c1.
        unfold correct_get_dst.match_res in c2.
        unfold correct_get_opcode_ins.match_res in c3.
        unfold stateless.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Branch *)
      eapply correct_statement_switch with (n:= 5).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
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
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_get_dst.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src64 _) ... *)
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
        get_invariant _op.
        get_invariant _ins.
        exists (v::v0::v1::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1,p2; reflexivity.
        intros; simpl.
        unfold correct_get_opcode_ins.match_res in c0.
        unfold correct_eval_ins.match_res in c1.
        unfold stateless.
        intuition eauto.

        intros.

        assert (Heq:
              step_opcode_branch x4 x6 x x5 x1 =
              bindM (step_opcode_branch x4 x6 x x5 x1) (fun _ : unit => returnM tt)). {
          clear - st7.
          unfold step_opcode_branch, get_opcode_branch.
          unfold bindM, returnM.
          destruct byte_to_opcode_branch; try reflexivity; unfold upd_pc.
          destruct (x1 =? 5)%nat; try reflexivity.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality.
          intros.
          destruct (Int.cmpu Cle Int.zero (Int.add x x5) &&
     Int.cmpu Clt (Int.add x x5) (Int.repr (Z.of_nat (ins_len x0))))%bool; try reflexivity.
          Ltac simpl_funcExt := 
          match goal with
          | |- context[if ?X then _ else _] =>
            destruct X; [apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intros | reflexivity]
          end.
          all: simpl_funcExt; destruct (Int.cmpu Cle Int.zero (Int.add x x5) &&
     Int.cmpu Clt (Int.add x x5) (Int.repr (Z.of_nat (ins_len x0))))%bool; try reflexivity.
          destruct _bpf_get_call; try reflexivity.
          destruct p0.
          destruct cmp_ptr32_nullM; try reflexivity.
          destruct p0.
          destruct b; try reflexivity.
          destruct exec_function; try reflexivity.
          destruct p0.
          unfold upd_reg.
          destruct Val.longofintu; try reflexivity.

          destruct _bpf_get_call; try reflexivity.
          destruct p0.
          destruct cmp_ptr32_nullM; try reflexivity.
          destruct p0.
          destruct b; try reflexivity.
          destruct exec_function; try reflexivity.
          destruct p0.
          unfold upd_reg.
          destruct Val.longofintu; try reflexivity.
        }
        rewrite Heq; clear Heq.
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
        unfold correct_step_opcode_branch.match_res. intuition.
        { instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_step_opcode_branch.match_res in H0.
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

          revert H11. (**r moves the hypotheses  to the goal *)
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

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst64.
        get_invariant _src64.
        get_invariant _pc.
        get_invariant _ofs.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 ::v4:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4, p5.
        split.
        unfold correct_get_offset.match_res, int32_correct in c3.
        rewrite <- c3.
        simpl.
        reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c0.
        unfold correct_get_src64.match_res in c1.
        unfold correct_eval_pc.match_res in c2.
        unfold correct_get_offset.match_res in c3.
        unfold correct_get_opcode_ins.match_res in c4.
        unfold stateless, int32_correct in *.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_ld_imm *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (get_immediate _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_ld_imm x4 x x3 x1 =
              bindM (step_opcode_mem_ld_imm x4 x x3 x1) (fun _ : unit => returnM tt)). {
          clear - st6.
          unfold step_opcode_mem_ld_imm, get_opcode_mem_ld_imm.
          unfold bindM, returnM.
          destruct byte_to_opcode_mem_ld_imm; try reflexivity.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality.
          intros.
          destruct eval_ins_len; try reflexivity.
          destruct p0.
          destruct Int.ltu; try reflexivity.
          destruct eval_ins; try reflexivity.
          destruct p0.
          destruct get_immediate; try reflexivity.
          destruct p0.
          unfold upd_reg.
          destruct Val.orl; try reflexivity.
          destruct upd_pc_incr; try reflexivity.
          destruct p0.
          reflexivity.
        }
        rewrite Heq; clear Heq.
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
        unfold correct_step_opcode_mem_ld_imm.match_res. intuition.
        { instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_step_opcode_mem_ld_imm.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          repeat constructor;auto.

          revert H9. (**r moves the hypotheses  to the goal *)
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

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _imm.
        get_invariant _pc.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        unfold correct_get_immediate.match_res in c0.
        unfold correct_eval_pc.match_res in c1.
        unfold correct_get_dst.match_res in c2.
        unfold correct_get_opcode_ins.match_res in c3.
        unfold stateless.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_ld_reg *)
      eapply correct_statement_switch with (n:= 1).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (get_src _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
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
        get_invariant _src.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_get_src.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_addr_ofs _) ... *)
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
        get_invariant _src64.
        get_invariant _ofs.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c.
        unfold correct_get_offset.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_ld_reg x7 x x3 x1 =
              bindM (step_opcode_mem_ld_reg x7 x x3 x1) (fun _ : unit => returnM tt)). {
          clear.
          unfold step_opcode_mem_ld_reg, get_opcode_mem_ld_reg.
          unfold bindM, returnM.
          destruct byte_to_opcode_mem_ld_reg; try reflexivity.
          all: apply Coq.Logic.FunctionalExtensionality.functional_extensionality;
          intros.
          all: destruct check_mem; try reflexivity.
          all: destruct p0.
          all: destruct cmp_ptr32_nullM; try reflexivity.
          all: destruct p0.
          all: destruct b; try reflexivity.
          all: destruct load_mem; try reflexivity.
          all: destruct p0.
          all: destruct upd_reg; try reflexivity.
          all: destruct p0.
          all: reflexivity.
        }
        rewrite Heq; clear Heq.
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
        unfold correct_step_opcode_mem_ld_reg.match_res. intuition.
        { instantiate (1:= ins_block).
          instantiate (1 := mrs_block).
          unfold var_inv_preserve.
          unfold match_temp_env.
          intros.
          unfold correct_step_opcode_mem_ld_reg.match_res in H0.
          inversion H1; subst; clear H1.
          inversion H5; subst; clear H5.
          inversion H6; subst; clear H6.
          inversion H7; subst; clear H7.
          inversion H8; subst; clear H8.
          inversion H9; subst; clear H9.
          inversion H10; subst; clear H10.
          inversion H11; subst; clear H11.
          inversion H12; subst; clear H12.
          inversion H13; subst; clear H13.
          repeat constructor;auto.

          revert H12. (**r moves the hypotheses  to the goal *)
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

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _addr.
        get_invariant _pc.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4.
        split.
        reflexivity.
        intros; simpl.
        unfold correct_get_addr_ofs.match_res in c0.
        unfold correct_eval_pc.match_res in c1.
        unfold correct_get_dst.match_res in c2.
        unfold correct_get_opcode_ins.match_res in c3.
        unfold stateless.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_st_imm *)
      eapply correct_statement_switch with (n:= 2).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
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
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_get_dst.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_immediate _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_addr_ofs _) ... *)
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
        get_invariant _dst64.
        get_invariant _ofs.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c.
        unfold correct_get_offset.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_st_imm (rBPFValues.sint32_to_vint x6) x7 x x3 x1 =
              bindM (step_opcode_mem_st_imm (rBPFValues.sint32_to_vint x6) x7 x x3 x1) (fun _ : unit => returnM tt)). {
          clear.
          unfold step_opcode_mem_st_imm, get_opcode_mem_st_imm.
          unfold bindM, returnM.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality;
          intros.
          destruct byte_to_opcode_mem_st_imm; try reflexivity.
          all: destruct check_mem; try reflexivity.
          all: destruct p0.
          all: destruct cmp_ptr32_nullM; try reflexivity.
          all: destruct p0.
          all: destruct b; try reflexivity.
          all: destruct store_mem_imm; try reflexivity.
          all: destruct p0.
          all: reflexivity.
        }
        rewrite Heq; clear Heq.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        intros.
        instantiate (3:= false).
        instantiate (2:= (DList.DCons (stateM_correct state_block mrs_block ins_block)
    (DList.DCons (stateless val32_correct)
      (DList.DCons (stateless val32_correct)
        (DList.DCons (stateless int32_correct)
          (DList.DCons (stateless reg_correct)
            (DList.DCons (stateless opcode_correct)
                  (DList.DNil _)))))))).
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
        get_invariant _imm.
        get_invariant _addr.
        get_invariant _pc.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 :: v4:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4, p5.
        split.
        reflexivity.
        intros; simpl.
        unfold correct_get_immediate.match_res in c0.
        unfold correct_get_addr_ofs.match_res in c1.
        unfold correct_eval_pc.match_res in c2.
        unfold correct_get_dst.match_res in c3.
        unfold correct_get_opcode_ins.match_res in c4.
        unfold stateless.
        unfold rBPFValues.sint32_to_vint.
        unfold int32_correct in c0.
        unfold val32_correct.
        unfold val32_correct in c1.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_Mem_st_reg *)
      eapply correct_statement_switch with (n:= 3).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
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
        get_invariant _dst.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_get_dst.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_src _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (eval_reg _) ... *)
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
        get_invariant _src.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_get_src.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_offset _) ... *)
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
        get_invariant _ins.
        exists (v::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0; reflexivity.
        intros; simpl.
        unfold correct_eval_ins.match_res in c.
        unfold stateless.
        intuition eauto.
        intros.

        (** goal: correct_body _ _ (bindM (get_addr_ofs _) ... *)
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
        get_invariant _dst64.
        get_invariant _ofs.
        exists (v::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c.
        unfold correct_get_offset.match_res in c0.
        unfold stateless.
        intuition eauto.
        intros.

        assert (Heq:
              step_opcode_mem_st_reg x6 x8 x x3 x1 =
              bindM (step_opcode_mem_st_reg x6 x8 x x3 x1) (fun _ : unit => returnM tt)). {
          clear.
          unfold step_opcode_mem_st_reg, get_opcode_mem_st_reg.
          unfold bindM, returnM.
          apply Coq.Logic.FunctionalExtensionality.functional_extensionality;
          intros.
          destruct byte_to_opcode_mem_st_reg; try reflexivity.
          all: destruct check_mem; try reflexivity.
          all: destruct p0.
          all: destruct cmp_ptr32_nullM; try reflexivity.
          all: destruct p0.
          all: destruct b; try reflexivity.
          all: destruct store_mem_reg; try reflexivity.
          all: destruct p0.
          all: reflexivity.
        }
        rewrite Heq; clear Heq.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        intros.
        instantiate (3:= false).
        instantiate (2:= (DList.DCons (stateM_correct state_block mrs_block ins_block)
    (DList.DCons (stateless val64_correct)
      (DList.DCons (stateless val32_correct)
        (DList.DCons (stateless int32_correct)
          (DList.DCons (stateless reg_correct)
            (DList.DCons (stateless opcode_correct)
                (DList.DNil _)))))))).
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
        get_invariant _src64.
        get_invariant _addr.
        get_invariant _pc.
        get_invariant _dst.
        get_invariant _op.
        exists (v ::v0::v1::v2 ::v3 :: v4:: nil).
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3, p4, p5.
        split.
        reflexivity.
        intros; simpl.
        unfold correct_eval_reg.match_res in c0.
        unfold correct_get_addr_ofs.match_res in c1.
        unfold correct_eval_pc.match_res in c2.
        unfold correct_get_dst.match_res in c3.
        unfold correct_get_opcode_ins.match_res in c4.
        unfold stateless.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opc.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode.match_res in c.
        unfold opcode_step_correct in c.
        assumption.
      + compute. intuition congruence.
    - (**r op_BPF_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          correct_get_opcode.match_res op_BPF_ILLEGAL_INS n st4 m4 /\
          n = Vint (Int.repr (Z.of_nat i)) /\
          (i <> 0x00 /\ i <> 0x01 /\ i <> 0x02 /\ i <> 0x03 /\ i <> 0x04 /\ i <> 0x05 /\ i <> 0x07)%nat /\
          (i <= 255)%nat /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le4 m4
            (Etempvar _opc Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat i)))).
        {
          get_invariant _opc.
          unfold correct_get_opcode.match_res in c.
          exists v.
          assert (c':=c).
          unfold opcode_correct in c'.
          destruct c' as (i & V & ILL & RANGE).
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
        repeat match goal with
        | |- context[Coqlib.zeq ?x (Z.of_nat i)] =>
            destruct (Coqlib.zeq x (Z.of_nat i)) ; try lia
        end.
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
        intros.
        eapply correct_function_modifies_more with (mods' := [state_block]).
        revert a.
        typeclasses eauto.
        unfold incl.
        intros.
        unfold In in *.
        intuition.
        unfold correct_upd_flag.match_res. tauto.
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
          repeat constructor;auto.

          revert H9. (**r moves the hypotheses  to the goal *)
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
        unfold stateless, flag_correct, int_of_flag; simpl.
        intuition congruence.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu64.match_res.
        intros.
        get_invariant _st.
        unfold stateM_correct in c.
        destruct c as (_ & c); auto.
        reflexivity.
Admitted.

End Step.

Close Scope Z_scope.

Existing Instance correct_function3_step.
