From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_get_immediate correct_eval_immediate correct_get_src correct_eval_reg.

(**
Check get_src64.
get_src64
     : nat -> int64 -> M val

 *)

Open Scope Z_scope.

Section Get_src64.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_src64.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_src64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    dcons (fun x => StateLess is_state_handle)
      (dcons (fun x => StateLess (opcode_correct x))
        (dcons (fun x => StateLess (int64_correct x))
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x  => StateLess (val64_correct x).

  Instance correct_function_get_src64 : forall a, correct_function p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app, get_src64.
    intros.

    eapply correct_statement_if_body_expr. intro EXPR.
    destruct Int.eq eqn: Heq.
    - eapply correct_statement_seq_body with (modifies1:=ModNothing).
      change_app_for_statement.
      eapply correct_statement_call with (has_cast := false).
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

      intros.
      correct_Forall.
      get_invariant _ins.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      intros; simpl. (**r TODO: need a verifier information ... *)
      tauto.

      intros.
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
      prove_in_inv.
      prove_in_inv.
      reflexivity.
      reflexivity.

      intros.
      correct_Forall.
      get_invariant _imm.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      intros; simpl.
      unfold correct_get_immediate.match_res in c1.
      tauto.
      intros.
      eapply correct_body_Sreturn_Some; eauto.
      intros.
      get_invariant _imm64.
      unfold correct_eval_immediate.match_res, val64_correct in c1.
      {
      destruct c1 as (Hv_eq & vl & Hvl_eq).
      subst.
      eexists.
      split_and.
      +
      unfold exec_expr, empty_env.
      rewrite p0. reflexivity.
      + unfold eval_inv. simpl.
      unfold val64_correct; simpl. eauto.
      + reflexivity.
      + simpl. auto.
      }
      reflexivity.
      reflexivity.
    - eapply correct_statement_seq_body with (modifies1:=ModNothing).
      change_app_for_statement.
      eapply correct_statement_call with (has_cast := false).
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

      intros.
      correct_Forall.
      get_invariant _ins.
      exists (v::nil).
      split_and.
      { unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      }
      { intros; simpl.
      unfold int64_correct.
      tauto.
      }
      intros.
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
      prove_in_inv.
      prove_in_inv.
      reflexivity.
      reflexivity.

      intros.
      correct_Forall.
      simpl in H.
      get_invariant _st.
      get_invariant _src.
      exists (v::v0::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0, p1.
      reflexivity.
      intros; simpl.
      unfold correct_get_src.match_res in c2.
      unfold eval_inv in *.
      tauto.

      intros.
      instantiate (1 := ModNothing).
      eapply correct_body_Sreturn_Some; eauto.
      intros.
      get_invariant _src64.
      unfold eval_inv, correct_eval_reg.match_res, val64_correct in c1.
      destruct c1 as (Hv_eq & vl & Hvl_eq).
      subst.
      eexists.
      split_and.
      { unfold exec_expr, empty_env.
        rewrite p0; reflexivity.
      }
      { unfold eval_inv. simpl.
      unfold val64_correct; simpl; eauto.
      }
      reflexivity.
      simpl ; auto.
      reflexivity.
      reflexivity.
    - reflexivity.
    - intros MS MT.
      get_invariant _x.
      unfold exec_expr.
      rewrite p0.
      simpl.
      unfold eval_inv, opcode_correct in c1.
      destruct c1 as (Hv_eq & Hc_le); subst.
      unfold Cop.sem_and, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
      reflexivity.
  Qed.

End Get_src64.
Close Scope Z_scope.

Existing Instance correct_function_get_src64.
