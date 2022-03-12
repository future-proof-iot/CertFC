From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From bpf.monadicmodel Require Import Opcode.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib CommonLemmaNat.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_opcode_alu32 correct_upd_reg correct_upd_flag correct_reg64_to_reg32.


(**
Check step_opcode_alu32.
step_opcode_alu32
     : val -> val -> reg -> nat -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_alu32.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (val:Type); (reg:Type); (nat:Type)].

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M unit) := step_opcode_alu32.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_alu32.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess is_state_handle)
      (dcons (stateless val32_correct)
       (dcons (stateless val32_correct)
          (dcons (stateless reg_correct)
            (dcons (stateless opcode_correct)
                    (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : unit -> Inv := fun _ => StateLess (eq Vundef).

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

  Instance correct_function_step_opcode_alu32 : forall a, correct_function p args unit f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, step_opcode_alu32.
    simpl.
    (** goal: correct_body _ _ (bindM (get_opcode_alu32 _) ... *)
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
              | op_BPF_ADD32 => bindM (upd_reg ... *)
    intros.
    unfold INV.
    destruct x eqn: Halu. (**r case discussion on each alu32_instruction *)
    - (**r op_BPF_ADD32 *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.repr (Int.unsigned (Int.add vl1 vl2))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation.
        unfold Cop.sem_add.
        unfold Cop.classify_add, typeof; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None. (** from `upd_flag DxFlag.BPF_OK` to `bindM (upd_flag DxFlag.BPF_OK) returnM` *)
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        get_invariant _st.
        reflexivity.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_SUB32 *)
      eapply correct_statement_switch with (n:= 16).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.repr (Int.unsigned (Int.sub vl1 vl2))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_sub, Cop.classify_sub; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        reflexivity.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MUL32 *)
      eapply correct_statement_switch with (n:= 32).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.repr (Int.unsigned (Int.mul vl1 vl2))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_mul, Cop.sem_binarith; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        reflexivity.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_DIV32 *)
      eapply correct_statement_switch with (n:= 48).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r correct_body p unit (if rBPFValues.compl_ne c0 val32_zero then ... *)
        eapply correct_statement_if_body_expr. intro EXPR.
        change Vzero with (Vint Int.zero).
        unfold rBPFValues.comp_ne_32.
        destruct (match c0 with
                  | Vint n1 => negb (Int.eq n1 Int.zero)
                  | _ => false
                  end) eqn: Hdiv_zero.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        unfold rBPFValues.val32_divu, Val.divlu. (**r star here *)
        rewrite Bool.negb_true_iff in Hdiv_zero.
        
        exists (v ::v0 :: Vlong (Int64.repr (Int.unsigned (Int.divu vl1 vl2))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_div, Cop.sem_binarith; simpl.
        rewrite Hdiv_zero.
        unfold Cop.sem_cast; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        reflexivity.
        reflexivity.

        change (upd_flag Flag.BPF_ILLEGAL_DIV) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_DIV) (fun _ : unit => returnM tt)).
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_DIV) fn ... *)
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
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::Vint (Int.neg (Int.repr 9)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        reflexivity.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _src32.
        unfold exec_expr.
        rewrite p0. unfold Vzero, rBPFValues.comp_ne_32, Int.zero.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_0 & c3_vl & c3_1).
        subst.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_OR32 *)
      eapply correct_statement_switch with (n:= 64).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.repr (Int.unsigned (Int.or vl1 vl2))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_or, Cop.sem_binarith; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        reflexivity.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_AND64 *)
      eapply correct_statement_switch with (n:= 80).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: Vlong (Int64.repr (Int.unsigned (Int.and vl1 vl2))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_and, Cop.sem_binarith; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        reflexivity.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_LSH32 *)
      eapply correct_statement_switch with (n:= 96).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_lt_32.
        (**r correct_body p unit (if rBPFValues.compu_lt_32 ... *)
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct (match c0 with
                  | Vint n1 => Int.ltu n1 (Int.repr 32)
                  | _ => false
                  end) eqn: Hlt_32.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32. (*
        unfold stateless, stateM_correct in c3.
        destruct c3 as (Hv_eq & Hst); subst.
        unfold stateless, reg_correct in c4. *)
        unfold stateless, val32_correct in c5.
        destruct c5 as (Hv1_eq & (vl & Hvl_eq)); subst.
        unfold stateless, val32_correct in c6.
        destruct c6 as (Hv2_eq & (vi & Hvi_eq)); subst.
        exists (v :: v0 :: (Val.longofintu (Val.shl (Vint vl) (Vint vi))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_shl, Cop.sem_shift; simpl.
        change Int.iwordsize with (Int.repr 32).
        rewrite Hlt_32.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        reflexivity.
        reflexivity.

        change (upd_flag Flag.BPF_ILLEGAL_SHIFT) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_SHIFT) (fun _ : unit => returnM tt)).
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_SHIFT) fn ... *)
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
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) :: Vint (Int.neg (Int.repr 10)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, flag_correct, int_of_flag.
        simpl.
        intuition. reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        reflexivity.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (Hv_eq & vi & Hvi_eq); subst.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold correct_get_opcode_alu32.match_res, opcode_alu32_correct in c3.
        unfold exec_expr.
        rewrite p0. f_equal.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_RSH32 *)
      eapply correct_statement_switch with (n:= 112).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_lt_32.
        (**r correct_body p unit (if rBPFValues.compu_lt_32 ... *)
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct (match c0 with
                  | Vint n1 => Int.ltu n1 (Int.repr 32)
                  | _ => false
                  end) eqn: Hlt_32.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c5.
        destruct c5 as (Hv1_eq & (vl & Hvl_eq)); subst.
        unfold stateless, val32_correct in c6.
        destruct c6 as (Hv2_eq & (vi & Hvi_eq)); subst.
        exists (v :: v0 :: (Val.longofintu (Val.shru (Vint vl) (Vint vi))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_shr, Cop.sem_shift; simpl.
        change Int.iwordsize with (Int.repr 32).
        rewrite Hlt_32.
        unfold Cop.sem_cast; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.


        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        reflexivity.
        reflexivity.

        change (upd_flag Flag.BPF_ILLEGAL_SHIFT) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_SHIFT) (fun _ : unit => returnM tt)).
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_SHIFT) fn ... *)
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
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) :: Vint (Int.neg (Int.repr 10)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, flag_correct, int_of_flag.
        simpl.
        intuition.
        reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        intros.
        reflexivity.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _src32.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c3.
        destruct c3 as (Hv_eq & vi & Hvi_eq); subst.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold correct_get_opcode_alu32.match_res, opcode_alu32_correct in c3.
        unfold exec_expr.
        rewrite p0. f_equal.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_NEG64 *)
      eapply correct_statement_switch with (n:= 128).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct (c2 =? 132)%nat eqn: Hneg_eq.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v :: v0 :: Val.longofintu (Val.neg (Vint vl1)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2.
        unfold Cop.sem_unary_operation, typeof.
        unfold Cop.sem_neg; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
        reflexivity.
        reflexivity.

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
        unfold correct_upd_flag.match_res. intuition.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro H.
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::Vint (Int.neg (Int.repr 1)) :: nil). (**r star here: it should be -1 *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.
        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c3.
        destruct c3 as (Hv_eq & Hrange).
        rewrite <- Hv_eq.
        destruct (c2 =? 132)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c2)) (Int.repr 132) = false). {
          apply Int.eq_false.
          apply nat8_neq_k; auto; lia.
        }
        rewrite Hneq; clear Hneq.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 132 240))) with (Int.repr 128) in c3.
        assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MOD32 *)
      eapply correct_statement_switch with (n:= 144).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold Vzero.
        (**r correct_body p unit (if rBPFValues.compl_ne c0 valu32_zero then ... *)
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct (rBPFValues.comp_ne_32 c0 (Vint Int.zero)) eqn: Hmod_zero.


        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        unfold rBPFValues.val32_modu, Val.modu. (**r star here *)
        unfold rBPFValues.comp_ne_32 in Hmod_zero.
        rewrite Bool.negb_true_iff in Hmod_zero.
        rewrite Hmod_zero.
        exists (v ::v0 :: Val.longofintu (Vint (Int.modu vl1 vl2)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_mod, Cop.sem_binarith; simpl.
        rewrite Hmod_zero.
        unfold Cop.sem_cast; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless, val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.

        change (upd_flag Flag.BPF_ILLEGAL_DIV) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_DIV) (fun _ : unit => returnM tt)).
        unfold rBPFValues.comp_ne_32 in Hmod_zero.
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_DIV) fn ... *)
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
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::Vint (Int.neg (Int.repr 9)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,val32_correct.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.
        reflexivity.

        intros.
        get_invariant _src32.
        unfold exec_expr.
        rewrite p0. unfold rBPFValues.comp_ne_32, Int.zero.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_0 & c3_vl & c3_1).
        subst.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_XOR32 *)
      eapply correct_statement_switch with (n:= 160).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.

        exists (v ::v0 :: Val.longofintu (Vint (Int.xor vl1 vl2)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        unfold Cop.sem_binary_operation, typeof.
        unfold Cop.sem_xor, Cop.sem_binarith; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless, val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.


        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_MOV32 *)
      eapply correct_statement_switch with (n:= 176).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        (**r because upd_reg return unit, here we use *_unit? *)
        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32.
        unfold val32_correct,stateless in c5, c6.
        destruct c5 as (Hv1_eq & (vl1 & Hvl1_eq)); subst.
        destruct c6 as (Hv2_eq & (vl2 & Hvl2_eq)); subst.
        exists (v ::v0 :: (Val.longofintu (Vint vl2)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p3.
        unfold Cop.sem_cast, typeof, Cop.classify_cast; simpl.
        split; [reflexivity | ].
        intros; simpl.
        intuition.
        unfold stateless,val64_correct.
        split; [reflexivity | eexists ; reflexivity].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_alu32.match_res in c3.
        unfold opcode_alu32_correct in c3.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        change (Int.repr (Z.of_nat (Nat.land 180 240))) with (Int.repr 176) in c3.
        change (Int.repr (Z.of_nat (Nat.land 188 240))) with (Int.repr 176) in c3.
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_ARSH32 *)
      eapply correct_statement_switch with (n:= 192).
      + simpl.
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_lt_32.
        (**r correct_body p unit (if rBPFValues.compu_lt_32 ... *)
        eapply correct_statement_if_body_expr. intro EXPR.
        destruct (match c0 with
                  | Vint n1 => Int.ltu n1 (Int.repr 32)
                  | _ => false
                  end) eqn: Hlt_32.

        eapply correct_statement_seq_body_unit.
        change_app_for_statement.
        (**r goal: correct_statement p unit (app f a) fn (Scall None (Evar ... *)
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
        correct_Forall.
        get_invariant _st.
        get_invariant _dst.
        get_invariant _dst32.
        get_invariant _src32. (*
        unfold stateless, stateM_correct in c3.
        subst.
        unfold stateless, reg_correct in c4. *)
        unfold stateless, val32_correct in c5.
        destruct c5 as (Hv1_eq & (vl & Hvl_eq)).
        unfold correct_reg64_to_reg32.match_res, val32_correct in c6.
        destruct c6 as (Hv2_eq & (vi & Hvi_eq)); subst.
        exists (v ::v0 :: (Val.longofint (Val.shr (Vint vl) (Vint vi))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1, p2, p3.
        simpl.
        unfold Cop.sem_shr, Cop.sem_shift; simpl.
        change Int.iwordsize with (Int.repr 32).
        rewrite Hlt_32.
        unfold Cop.sem_cast; simpl.
        split.
        reflexivity.
        intros.
        unfold stateless, reg_correct, val64_correct.
        unfold eval_inv,is_state_handle in c3.
        simpl.
        intuition.
        eexists ; reflexivity.
        intros.


        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.

        change (upd_flag Flag.BPF_ILLEGAL_SHIFT) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_SHIFT) (fun _ : unit => returnM tt)).
        (**r goal: correct_body p unit (upd_flag Flag.BPF_ILLEGAL_SHIFT) fn ... *)
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
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) :: Vint (Int.neg (Int.repr 10)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, flag_correct, int_of_flag.
        simpl.
        intuition.
        reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.
        reflexivity.

        intros.
        get_invariant _src32.
        unfold correct_reg64_to_reg32.match_res, val32_correct in c3.
        destruct c3 as (Hv_eq & vi & Hvi_eq); subst.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.

      + reflexivity.
      + intros.
        get_invariant _opcode_alu32.
        unfold correct_get_opcode_alu32.match_res, opcode_alu32_correct in c3.
        unfold exec_expr.
        rewrite p0. f_equal.
        (* opcode_alu32_correct should be a mapping between opcodes and int *)
        destruct c3; assumption.
      + compute. intuition congruence.
    - (**r op_BPF_ALU64_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          eval_inv (correct_get_opcode_alu32.match_res op_BPF_ALU32_ILLEGAL_INS) n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\
          is_illegal_alu32_ins i /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_alu32 Clightdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat (Nat.land i 240))))).
        {
          get_invariant _opcode_alu32.
          unfold correct_get_opcode_alu32.match_res in c3.
          exists v.
          assert (c3':=c3).
          unfold opcode_alu32_correct in c3'.
          destruct c3' as (i & V & ILL).
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
        unfold is_illegal_alu32_ins in Hill.
        repeat match goal with
        | |- context[Coqlib.zeq ?x (Z.of_nat (Nat.land i 240))] =>
            destruct (Coqlib.zeq x (Z.of_nat (Nat.land i 240))) ; try lia
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
        typeclasses eauto.
        unfold correct_upd_flag.match_res. tauto.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.

        unfold INV; intro HH.
        correct_Forall.
        get_invariant _st.
        unfold eval_inv,is_state_handle in c3.
        subst.
        exists ((Vptr st_blk Ptrofs.zero) ::
                (Vint (Int.neg (Int.repr 1))) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        unfold Cop.sem_unary_operation; simpl.
        split.
        reflexivity.
        intros.
        unfold stateless, flag_correct, int_of_flag; simpl.
        split; auto.
        reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        unfold match_res, correct_get_opcode_alu32.match_res.
reflexivity.        reflexivity.
Qed.

End Step_opcode_alu32.

Close Scope Z_scope.

Existing Instance correct_function_step_opcode_alu32.
