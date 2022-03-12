From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From bpf.monadicmodel Require Import Opcode.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_opcode_branch correct_upd_pc
correct_upd_flag correct__bpf_get_call correct_cmp_ptr32_nullM correct_exec_function correct_upd_reg.

(**
Check step_opcode_branch.
step_opcode_branch
     : val64_t ->
       val64_t -> DxIntegers.sint32_t -> DxIntegers.sint32_t -> nat8 -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_branch.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (val:Type); (int:Type); (int:Type); (nat:Type)].

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M unit) := step_opcode_branch.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_branch.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess is_state_handle)
      (dcons (stateless val64_correct)
       (dcons (stateless val64_correct)
          (dcons (stateless int32_correct)
          (dcons (stateless int32_correct)
            (dcons (stateless opcode_correct)
                    (DList.DNil _))))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun _ => StateLess (eq Vundef).

Ltac correct_forward L :=
  match goal with
  | |- @correct_body _ _ (bindM ?F1 ?F2)  _
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
  | |- @correct_body _ _ (match  ?x with true => _ | false => _ end) _
                     (Sifthenelse _ _ _)
                     _ _ _ _ _ _ _ =>
      eapply correct_statement_if_body; [prove_in_inv | destruct x ]
  end.

  Lemma Cop_add : forall vl1 vl2 m,
       Cop.sem_binary_operation (globalenv p) Cop.Oadd
                                (Vlong vl1) Clightdefs.tulong (Vlong vl2) Clightdefs.tulong m =
         Some (Vlong (Int64.add vl1 vl2)).
  Proof.
    reflexivity.
  Qed.

  Instance correct_function_step_opcode_branch : forall a, correct_function p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, step_opcode_branch.
    simpl.
    (** goal: correct_body _ _ (bindM (get_opcode_branch _) ... *)
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
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv,int32_correct,stateless in c5, c6; subst.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless, int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
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
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        unfold eval_inv, is_state_handle in c4.
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
reflexivity.        reflexivity.
        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c4.
        destruct c4 as (Hv_eq & Hrange).
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
          apply nat8_neq_k; auto; lia.
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
        change (Int.repr (Z.of_nat (Nat.land 5 240))) with (Int.repr 0) in c4.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_JEQ *)
      eapply correct_statement_switch with (n:= 0x10).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_eq.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in *.
        unfold int32_correct,stateless in c5, c6; subst.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 21 240))) with (Int.repr 0x10) in c4.
        change (Int.repr (Z.of_nat (Nat.land 29 240))) with (Int.repr 0x10) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JGT *)
      eapply correct_statement_switch with (n:= 0x20).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_gt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in *.
        unfold int32_correct,stateless in c5, c6; subst.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 37 240))) with (Int.repr 0x20) in c4.
        change (Int.repr (Z.of_nat (Nat.land 45 240))) with (Int.repr 0x20) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JGE *)
      eapply correct_statement_switch with (n:= 0x30).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_ge.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 53 240))) with (Int.repr 0x30) in c4.
        change (Int.repr (Z.of_nat (Nat.land 61 240))) with (Int.repr 0x30) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JLT *)
      eapply correct_statement_switch with (n:= 0xa0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_lt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 165 240))) with (Int.repr 0xa0) in c4.
        change (Int.repr (Z.of_nat (Nat.land 173 240))) with (Int.repr 0xa0) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JLE *)
      eapply correct_statement_switch with (n:= 0xb0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_le.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 181 240))) with (Int.repr 0xb0) in c4.
        change (Int.repr (Z.of_nat (Nat.land 189 240))) with (Int.repr 0xb0) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSET *)
      eapply correct_statement_switch with (n:= 0x40).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.complu_set.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 69 240))) with (Int.repr 0x40) in c4.
        change (Int.repr (Z.of_nat (Nat.land 77 240))) with (Int.repr 0x40) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JNE *)
      eapply correct_statement_switch with (n:= 0x50).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_ne.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 85 240))) with (Int.repr 0x50) in c4.
        change (Int.repr (Z.of_nat (Nat.land 93 240))) with (Int.repr 0x50) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSGT *)
      eapply correct_statement_switch with (n:= 0x60).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_gt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 101 240))) with (Int.repr 0x60) in c4.
        change (Int.repr (Z.of_nat (Nat.land 109 240))) with (Int.repr 0x60) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSGE *)
      eapply correct_statement_switch with (n:= 0x70).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_ge.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 117 240))) with (Int.repr 0x70) in c4.
        change (Int.repr (Z.of_nat (Nat.land 125 240))) with (Int.repr 0x70) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSLT *)
      eapply correct_statement_switch with (n:= 0xc0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_lt.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 197 240))) with (Int.repr 0xc0) in c4.
        change (Int.repr (Z.of_nat (Nat.land 205 240))) with (Int.repr 0xc0) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSLE *)
      eapply correct_statement_switch with (n:= 0xd0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compl_le.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.add c1 c2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,int32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.
        intros.
        get_invariant _dst64.
        get_invariant _src64.
        unfold stateless, val64_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        unfold stateless, val64_correct in c5.
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
        change (Int.repr (Z.of_nat (Nat.land 213 240))) with (Int.repr 0xd0) in c4.
        change (Int.repr (Z.of_nat (Nat.land 221 240))) with (Int.repr 0xd0) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_CALL *)
      eapply correct_statement_switch with (n:= 0x80).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)

        eapply correct_statement_if_body_expr. intro EXPR.

        destruct (c3 =? 133)%nat eqn: Hneg_eq.

        eapply correct_statement_seq_body with (modifies1:=ModNothing).
        change_app_for_statement.
        eapply correct_statement_call with (has_cast := false).
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        reflexivity.
        reflexivity.
        reflexivity.
        simpl.
        Hdisj_false.
        simpl.
        Hdisj_false.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _src64.
        unfold val64_correct,stateless in c4.
        destruct c4 as (Hv_eq & vl & Hvl_eq); subst.
        unfold rBPFValues.val_intsoflongu.
        exists ((Vint (Int.repr (Int64.unsigned vl))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, val32_correct.
        intuition eauto.
        intros.

        eapply correct_statement_seq_body with (modifies1:=ModNothing).
        change_app_for_statement.
        eapply correct_statement_call with (has_cast := true).
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        reflexivity.
        reflexivity.
        reflexivity.
        simpl.
        Hdisj_false.
        simpl.
        Hdisj_false.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _f_ptr.
        unfold eval_inv,correct__bpf_get_call.match_res, val_ptr_correct in c4.
        subst.
        unfold correct_cmp_ptr32_nullM.match_arg_list.
        exists (v :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        simpl.
        split; [reflexivity |].
        get_invariant _f_ptr. unfold eval_inv in c4.
        unfold correct__bpf_get_call.match_res  in c4.
        intros.
        unfold val_ptr_correct.
        intuition congruence.
        intros.


        eapply correct_statement_if_body_expr. intro EXPR0.
        destruct x1 eqn: Hx1_eq.

        change (upd_flag Flag.BPF_ILLEGAL_CALL) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_CALL) (fun _ : unit => returnM tt)).
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        normalise_post_unit.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.

        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall. simpl in H.
        get_invariant _st.
        exists (v ::Vint (Int.neg (Int.repr 4)) :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold stateless,flag_correct.
        intuition congruence.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.

        eapply correct_statement_seq_body with (modifies1:=ModNothing).
        change_app_for_statement.
        eapply correct_statement_call with (has_cast := false).
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        reflexivity.
        reflexivity.
        reflexivity.
        simpl.
        Hdisj_false.
        simpl.
        Hdisj_false.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall. simpl in H.
        get_invariant _st.
        get_invariant _f_ptr.
        unfold eval_inv, is_state_handle in c4.
        unfold eval_inv,correct__bpf_get_call.match_res, val_ptr_correct in c5.
        unfold correct_exec_function.match_arg_list.
        exists (v :: v0 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        simpl.
        split; [reflexivity |].
        intros.
        intuition congruence.
        intros.

        assert (Heq: (upd_reg R0 (Val.longofintu x2)) =
          (bindM (upd_reg R0 (Val.longofintu x2)) (fun _ : unit => returnM tt))). {
          unfold bindM, returnM.
          unfold upd_reg.
          destruct Val.longofintu; reflexivity.
        }
        rewrite Heq; clear Heq.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        normalise_post_unit.
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_reg.match_res. intuition.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall. simpl in H.
        get_invariant _st.
        get_invariant _res.
        unfold eval_inv, is_state_handle in c4.
        unfold eval_inv,correct_exec_function.match_res, val32_correct in c5.
        destruct c5 as (Hv0_eq & vi & Hvi_eq); subst.
        exists (Vptr st_blk Ptrofs.zero :: (Vint (Int.repr 0)) :: (Val.longofintu (Vint vi)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, reg_correct, val64_correct.
        intuition eauto.
        reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res.
reflexivity.        reflexivity.

        all: try reflexivity.

        intros.
        get_invariant _is_null.
        unfold exec_expr, Val.of_bool.
        rewrite p0.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c4.
        rewrite c4.
        unfold Vtrue, Vfalse.
        destruct x1; reflexivity.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        unfold eval_inv, is_state_handle in c4.
        exists (v :: (Vint (Int.neg (Int.repr 1))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, flag_correct, int_of_flag; simpl.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c4.
        destruct c4 as (Hv_eq & Hrange).
        rewrite <- Hv_eq.
        destruct (c3 =? 133)%nat eqn: Hc3_eq.
        rewrite Nat.eqb_eq in Hc3_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc3_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c3)) (Int.repr 133) = false). {
          apply Int.eq_false.
          apply nat8_neq_k; auto; lia.
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
        change (Int.repr (Z.of_nat (Nat.land 133 240))) with (Int.repr 0x80) in c4.
        assumption.
      + compute. intuition congruence.
    - (**r op_BPF_RET *)
      eapply correct_statement_switch with (n:= 0x90).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)

        eapply correct_statement_if_body_expr. intro EXPR.

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
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
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
reflexivity.        reflexivity.
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
        eapply correct_statement_call_none.
        my_reflex.
        reflexivity.
        reflexivity.
        typeclasses eauto.
        unfold correct_upd_flag.match_res. intuition.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        exists (v ::Vint (Int.repr (-1)) :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold stateless,flag_correct.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c4.
        destruct c4 as (Hv_eq & Hrange).
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
          apply nat8_neq_k; auto; lia.
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
        change (Int.repr (Z.of_nat (Nat.land 149 240))) with (Int.repr 0x90) in c4.
        destruct c4; intuition.
      + compute. intuition congruence.

    - (**r op_BPF_JMP_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          eval_inv (correct_get_opcode_branch.match_res op_BPF_JMP_ILLEGAL_INS) n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\
          is_illegal_jmp_ins i /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_jmp Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat (Nat.land i 240))))).
        {
          get_invariant _opcode_jmp.
          unfold correct_get_opcode_branch.match_res in c4.
          exists v.
          assert (c4':=c4).
          unfold opcode_branch_correct in c4'.
          destruct c4' as (i & V & ILL).
          exists i.
          split ; auto.
          split ; auto.
          split ; auto.
          unfold exec_expr. congruence.
        }
        destruct Hillegal_ins as (n & i & Hprop & Hn_eq & Hill & EX).
        exists (Z.of_nat (Nat.land i 240)).
        split; auto.
        split.

        change Int.modulus with 4294967296.
        assert (Hand_le: (Nat.land 240 i <= 240)%nat). {
          apply LemmaNat.land_bound.
        }
        rewrite Nat.land_comm.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        unfold is_illegal_jmp_ins in Hill.
        repeat match goal with
        | |- context[Coqlib.zeq ?x (Z.of_nat (Nat.land i 240))] =>
            destruct (Coqlib.zeq x (Z.of_nat (Nat.land i 240))) ; try lia
        end.
        (* default *)
        simpl.
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
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H1.
        correct_Forall.
        get_invariant _st.
        get_invariant _pc.
        get_invariant _ofs.
        unfold eval_inv in * ; unfold int32_correct,stateless in c5,c6.
        exists (v :: Vint (Int.repr (-1)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split. reflexivity.
        subst.
        intros.
        simpl.
        unfold stateless,flag_correct, int_of_flag; simpl.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_branch.match_res.
reflexivity.        reflexivity.
Qed.

End Step_opcode_branch.

Close Scope Z_scope.

Existing Instance correct_function_step_opcode_branch.
