From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Flag Regs State Monad rBPFAST rBPFValues.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values AST Clight Memory Memtype Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import correct_upd_flag correct_eval_ins_len correct_eval_pc correct_step correct_upd_pc_incr.

Open Scope Z_scope.


(**
Check bpf_interpreter_aux.
bpf_interpreter_aux
     : nat -> M unit
*)

Section Bpf_interpreter_aux.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := bpf_interpreter_aux.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Variable modifies : list block. (* of the C code *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_interpreter_aux.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (stateless nat_correct_overflow)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef.

Lemma bpf_interpreter_aux_eq: forall n,
  bpf_interpreter_aux n =
    if Nat.eqb n 0 then bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt)
    else bindM eval_ins_len (fun len => 
          (bindM eval_pc (fun pc =>
            if (andb (Int_leu Int.zero pc) (Int.ltu pc len)) then
              (bindM rBPFInterpreter.step (fun _ =>
                (bindM eval_flag (fun f =>
                  if flag_eq f BPF_OK then
                    (bindM upd_pc_incr (fun _ =>
                      bpf_interpreter_aux (Nat.pred n)))
                  else
                    returnM tt))))
            else
              bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt)))).
Proof.
  destruct n.
  - simpl. intros; reflexivity.
  - intros.
    simpl.
    reflexivity.
Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma mod_eq : forall (x y:Z), (x >= 0 -> y > 0 -> x mod y = x -> x < y)%Z.
Proof.
  intros.
  zify.
  intuition subst ; try lia.
Qed.


  Instance correct_function3_bpf_interpreter_aux : forall a, correct_function3 p args res f fn (state_block::modifies) false match_arg_list match_res a.
  Proof.
    intros.
    unfold args in a.
    car_cdr.
    revert c.
    induction c.
    {
      intros.
      correct_function_from_body args.
      unfold f. unfold app. intros. rewrite bpf_interpreter_aux_eq.
      remember (0 =? 0)%nat as cmp.
      simpl.
      rewrite Heqcmp.
      apply correct_statement_if_body_expr.
      intros. simpl.

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
        unfold correct_upd_flag.match_res in H0.
        inversion H1; subst; clear H1.
        inversion H5; subst; clear H5.
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

      intro HH.
      correct_Forall.
      cbn in HH.
      get_invariant _st.
      exists (v ::
              (Vint (Int.neg (Int.repr 5))) :: nil). (**r star here *)
      unfold map_opt, exec_expr.
      rewrite p0.
      unfold Cop.sem_unary_operation; simpl.
      split.
      reflexivity.
      intros.
      unfold stateless, flag_correct, CommonLib.int_of_flag; simpl.
      intuition congruence.
      intros.

      (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
      eapply correct_body_Sreturn_None.
      unfold match_res, correct_get_opcode_alu64.match_res.
      intros.
      cbn in H.
      get_invariant _st.
      unfold stateM_correct in c.
      destruct c as (_ & c); auto.
      reflexivity.

      reflexivity.

      intros.
      cbn in H.
      get_invariant _fuel.
      unfold exec_expr.
      rewrite p0.
      unfold stateless, nat_correct_overflow in c.
      destruct c as (c & _).
      rewrite <- c.
      unfold Cop.sem_binary_operation, typeof; simpl.
      unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
      unfold Val.of_bool.
      rewrite Int.eq_true.
      reflexivity.
    }

    intros.
    correct_function_from_body args.
    correct_body.
    unfold f, app.
    rewrite bpf_interpreter_aux_eq.
    eapply correct_statement_if_body_expr. intro EXPR.
    simpl.
    (**r check _fuel in INV *)
    apply correct_statement_seq_set with (match_res1 := fun _ => stateless nat_correct c).
    +
      intros.
      unfold INV in H.
      get_invariant _fuel.
      get_invariant _st.
      unfold stateless, nat_correct_overflow in c0.
      destruct c0 as (c0 & Hc0_range).
      subst.
      eexists.
      split.
      {
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_sub; simpl.
        unfold Cop.sem_binarith; simpl.
        unfold Int.sub.
        fold Int.one; rewrite Int.unsigned_one.
        rewrite Zpos_P_of_succ_nat.
        rewrite <- Nat2Z.inj_succ.
        rewrite Int.unsigned_repr; [ | lia].
        rewrite Nat2Z.inj_succ.
        rewrite <- Z.add_1_r.
        rewrite Z.add_simpl_r.
        reflexivity.
      }
      split.
      {
        unfold stateless, nat_correct.
        reflexivity.
      }
    constructor.
    simpl.
    reflexivity.
  +
    unfold INV.
    simpl. intuition subst ; discriminate.
  +
    intros.
    (**r correct_body _ _ (bindM (eval_ins_len _ _) ... *)
    eapply correct_statement_seq_body with (modifies1:=nil);eauto.
    unfold typeof.
    change_app_for_statement.
    eapply correct_statement_call with (has_cast:=false).
    my_reflex.
    reflexivity.
    reflexivity.
    intros.
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
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    intuition eauto.
    intros.

    (**r correct_body _ _ (bindM (eval_pc _ _) ... *)
    eapply correct_statement_seq_body with (modifies1:=nil);eauto.
    unfold typeof.
    change_app_for_statement.
    eapply correct_statement_call with (has_cast:=false).
    my_reflex.
    reflexivity.
    reflexivity.
    intros.
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
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    intuition eauto.
    intros.

    unfold Int_leu.
    admit. (*
    destruct (negb (Int.ltu _ _) && Int.ltu _ _) eqn: Hcond.

    2:{
      eapply correct_statement_seq_body_unit.
      change_app_for_statement.
      unfold app.
      unfold correct_statement.
      change (upd_flag BPF_ILLEGAL_LEN) with
        (if false then upd_flag BPF_ILLEGAL_LEN else 
          (bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt))).
      TBC...
    }

    eapply correct_statement_if_body_expr. clear EXPR. intro EXPR.
    destruct x2.
    2:{
       destruct (exec_expr (globalenv p) empty_env le3 m3
          (Etempvar _check_mem (Clightdefs.tptr Clightdefs.tuchar))) eqn:CHK.
      - eapply correct_body_Sreturn_Some with (v:=v).
        intros.
        split. rewrite CHK. auto.
        split.
        get_invariant _check_mem.
        unfold exec_expr in CHK. assert (v0 = v) by congruence. subst.
        unfold correct_bpf_interpreter_aux2.match_res, val_ptr_correct in c4.
        destruct c4 as (Hv0_eq & _); subst.
        unfold match_res. unfold val_ptr_correct.
        split; auto. unfold INV in *.
        get_invariant _st.
        unfold stateM_correct in c4. destruct c4 ; auto.
        reflexivity.
        left. reflexivity.
     - repeat intro.
      get_invariant _check_mem.
      unfold exec_expr in CHK. congruence.
     }

    change_app_for_body.
    eapply correct_body_call_ret with (has_cast:=false).
    my_reflex.
    reflexivity.
    reflexivity.
    intros.
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

    unfold INV; intro H.
    correct_Forall.
    get_invariant _st.
    get_invariant _n.
    get_invariant _perm.
    get_invariant _chunk.
    get_invariant _addr.
    get_invariant _mrs.
    exists (v :: v0 :: v1 :: v2 :: v3 :: v4 :: nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3, p4, p5; reflexivity.
    simpl;intros.
    intuition eauto.
    reflexivity.

    intros.
    get_invariant _is_null.
    unfold exec_expr, Val.of_bool.
    rewrite p0.
    unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
    unfold Vtrue, Vfalse.
    rewrite c4.
    destruct x2; reflexivity.
    reflexivity.

    get_invariant _num.
    unfold stateless, nat_correct.
    unfold nat_correct_mrs_num in c4, c7.
    destruct c4 as (Hv_eq & Hrange).
    destruct c7 as (Hv2_eq & Hrange_v2).
    subst.
    reflexivity.

    intros.
    (**r goal: correct_body p val (bindM (bpf_interpreter_aux2 ... *)
    eapply correct_statement_seq_body with (modifies1:=nil);eauto.
    unfold typeof.
    change_app_for_statement.
    eapply correct_statement_call with (has_cast:=false).
    my_reflex.
    reflexivity.
    reflexivity.
    intros.
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
    get_invariant _cur_mr.
    get_invariant _perm.
    get_invariant _addr.
    get_invariant _chunk.
    get_invariant _mrs.
    get_invariant _st.
    unfold stateM_correct in c9.
    exists (v::v0::v1::v2::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3; reflexivity.
    simpl;intros.
    unfold correct_get_mem_region.match_res in c4.
    intuition eauto.

    intros.
    (**r goal: correct_body p val (bindM (cmp_ptr32_nullM ... *)
    eapply correct_statement_seq_body with (modifies1:=nil);eauto.
    {
      unfold typeof.
      change_app_for_statement.
      eapply correct_statement_call with (has_cast:=true).
      my_reflex.
      reflexivity.
      reflexivity.
      intros.
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
      get_invariant _check_mem.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      unfold correct_bpf_interpreter_aux2.match_res in c4.
      intuition eauto.
    }

    intros.
    (**r modifying here? *)
    eapply correct_statement_if_body_expr. clear EXPR. intro EXPR.
    destruct x2.
    2:{
       destruct (exec_expr (globalenv p) empty_env le3 m3
          (Etempvar _check_mem (Clightdefs.tptr Clightdefs.tuchar))) eqn:CHK.
      - eapply correct_body_Sreturn_Some with (v:=v).
        intros.
        split. rewrite CHK. auto.
        split.
        get_invariant _check_mem.
        unfold exec_expr in CHK. assert (v0 = v) by congruence. subst.
        unfold correct_bpf_interpreter_aux2.match_res, val_ptr_correct in c4.
        destruct c4 as (Hv0_eq & _); subst.
        unfold match_res. unfold val_ptr_correct.
        split; auto. unfold INV in *.
        get_invariant _st.
        unfold stateM_correct in c4. destruct c4 ; auto.
        reflexivity.
        left. reflexivity.
     - repeat intro.
      get_invariant _check_mem.
      unfold exec_expr in CHK. congruence.
     }

    change_app_for_body.
    eapply correct_body_call_ret with (has_cast:=false).
    my_reflex.
    reflexivity.
    reflexivity.
    intros.
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

    unfold INV; intro H.
    correct_Forall.
    get_invariant _st.
    get_invariant _n.
    get_invariant _perm.
    get_invariant _chunk.
    get_invariant _addr.
    get_invariant _mrs.
    exists (v :: v0 :: v1 :: v2 :: v3 :: v4 :: nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3, p4, p5; reflexivity.
    simpl;intros.
    intuition eauto.
    reflexivity.

    intros.
    get_invariant _is_null.
    unfold exec_expr, Val.of_bool.
    rewrite p0.
    unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
    unfold Vtrue, Vfalse.
    rewrite c4.
    destruct x2; reflexivity.
    reflexivity.*)

    instantiate (1:= state_block :: modifies).
    unfold union; simpl.
    admit.
  +
    reflexivity.
  + intro.
    unfold INV in H.
    get_invariant _fuel.
    unfold stateless, nat_correct_overflow in c0.
    destruct c0 as (Hv_eq & Hrange).
    unfold exec_expr.
    rewrite p0.
    simpl.
    rewrite <- Hv_eq.
    unfold Cop.sem_cmp, Cop.sem_binarith, Val.of_bool, Vfalse; simpl.
    unfold Int.eq.
    change (Int.unsigned (Int.repr 0)) with 0.
    rewrite Int.unsigned_repr;[ | lia].
    assert (Hneq: (Z.succ (Z.of_nat c)) <> 0). {
      lia.
    }
    eapply zeq_false with (a:= true) (b:= false) in Hneq.
    rewrite Zpos_P_of_succ_nat.
    rewrite Hneq.
    reflexivity.
Admitted.

End Bpf_interpreter_aux.

Close Scope Z_scope.

Existing Instance correct_function3_bpf_interpreter_aux.
