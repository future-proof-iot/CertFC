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
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (int:Type); (reg:Type); (nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := step_opcode_mem_ld_reg.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_mem_ld_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
  (dcons (fun _ => StateLess is_state_handle)
    (dcons (stateless val32_correct)
      (dcons (stateless int32_correct)
        (dcons (stateless reg_correct)
          (dcons (stateless opcode_correct)
                (DList.DNil _)))))).

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

  Instance correct_function_step_opcode_mem_ld_reg : forall a, correct_function p args res f fn modifies false match_state match_arg_list match_res a.
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
        unfold eval_inv, is_state_handle in c3; unfold stateless in c4.
        eauto.

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
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv, is_state_handle in c3.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        reflexivity.
        reflexivity.

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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 4)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold eval_inv, is_state_handle in c3; unfold correct_check_mem.match_res, val_ptr_correct in c4.
        split; [intuition|].
        split; [reflexivity|].
        tauto.

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
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        reflexivity.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _is_null.
        unfold eval_inv,correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold eval_inv, correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
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
        unfold eval_inv, stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        unfold eval_inv, is_state_handle in c3; unfold stateless in c4.
        eauto.

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
        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold eval_inv, is_state_handle in c3.
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
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv, is_state_handle in c3.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        reflexivity.
        reflexivity.


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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 2)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold eval_inv, stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold eval_inv, is_state_handle in c3; unfold correct_check_mem.match_res, val_ptr_correct in c4.
        split; [intuition|].
        split; [reflexivity|].
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
        unfold eval_inv, is_state_handle in c3.
        unfold correct_load_mem.match_res in c5.
        intuition eauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        reflexivity.
        reflexivity.

        reflexivity.

        intros.
        get_invariant _is_null.
        unfold eval_inv,correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold eval_inv,correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
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
        unfold eval_inv, stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        unfold eval_inv, is_state_handle in c3; unfold stateless in c4.
        eauto.

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
        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold eval_inv, is_state_handle in c3.
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
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv, is_state_handle in c3.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        reflexivity.
        reflexivity.

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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 1)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold eval_inv, stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold eval_inv, is_state_handle in c3; unfold correct_check_mem.match_res, val_ptr_correct in c4.
        split; [intuition|].
        split; [reflexivity|].
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
        unfold eval_inv, is_state_handle in c3.
        unfold correct_load_mem.match_res in c5.
        intuition eauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        intros.
        get_invariant _st.
        unfold eval_inv, is_state_handle in c3.
        reflexivity.
        reflexivity.
        reflexivity.

        intros.
        get_invariant _is_null.
        unfold eval_inv,correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold eval_inv,correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
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
        unfold eval_inv, stateless, perm_correct, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z.
        unfold eval_inv, is_state_handle in c3; unfold stateless in c4.
        eauto.

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
        get_invariant _st.
        get_invariant _addr_ptr.
        exists (v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p1.
        reflexivity.
        intros; simpl.
        unfold val_ptr_correct.
        unfold eval_inv, is_state_handle in c3.
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
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag, CommonLib.Z_of_flag.
        unfold eval_inv, is_state_handle in c3.
        rewrite Int.neg_repr.
        tauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        reflexivity.
        reflexivity.

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
        get_invariant _st.
        get_invariant _addr_ptr.
        get_invariant _is_null.
        exists (v::Vint (Int.repr 8)::v0::nil).
        split.
        unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity.
        intros; simpl.
        unfold eval_inv, stateless, match_chunk, rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z, val_ptr_correct.
        unfold eval_inv, is_state_handle in c3; unfold eval_inv,correct_check_mem.match_res, val_ptr_correct,stateless in c4.
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
        unfold eval_inv, is_state_handle in c3.
        unfold correct_load_mem.match_res in c5.
        intuition eauto.

        intros.
        eapply correct_body_Sreturn_None.
        unfold match_res.
        reflexivity.
        reflexivity.

        reflexivity.

        intros.
        get_invariant _is_null.
        unfold eval_inv,correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        unfold exec_expr. rewrite p0.
        subst.
        unfold Val.of_bool, Vtrue, Vfalse.
        destruct x1; reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_ld.
        unfold eval_inv,correct_get_opcode_mem_ld_reg.match_res, opcode_mem_ld_reg_correct in c3.
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
          eval_inv (correct_get_opcode_mem_ld_reg.match_res op_BPF_LDX_REG_ILLEGAL_INS) n st0 m0 /\
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
        unfold eval_inv, stateless, flag_correct, CommonLib.int_of_flag; simpl.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        eapply correct_body_Sreturn_None.
        reflexivity.
        reflexivity.
  Qed.

End Step_opcode_mem_ld_reg.

Close Scope Z_scope.

Existing Instance correct_function_step_opcode_mem_ld_reg.
