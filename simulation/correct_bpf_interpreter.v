From bpf.comm Require Import MemRegion State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.

From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.proof Require Import clight_exec Clightlogic CorrectRel MatchState CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import correct_eval_mrs_regions correct_get_mem_region correct_upd_reg correct_bpf_interpreter_aux correct_eval_flag correct_eval_reg.


(**
Check bpf_interpreter.
bpf_interpreter
     : nat -> M val
*)

Section Bpf_interpreter.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := bpf_interpreter.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_interpreter.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list :DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess is_state_handle)
      (dcons (stateless nat_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x => StateLess (val64_correct x).

  Instance correct_function_bpf_interpreter : forall a, correct_function p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app.
    unfold bpf_interpreter.
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

    unfold INV; intro H.
    correct_Forall.
    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    intuition eauto.
    intros.

    instantiate (1:= ModSomething). (**r TODO: right? *)

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

    unfold INV; intro H.
    correct_Forall.
    get_invariant _mrs.
    exists ((Vint (Int.repr 0))::v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold correct_eval_mrs_regions.match_res in c0.
    unfold stateless, nat_correct.
    intuition eauto.
    change Int.max_unsigned with 4294967295%Z.
    lia.
    intros.

    instantiate (1:= ModSomething). (**r TODO: right? *)

    eapply correct_statement_seq_body with (modifies1:=ModSomething).
    change_app_for_statement.
    eapply correct_statement_call with (has_cast := false).
    my_reflex.
    reflexivity.
    reflexivity.
    apply correct_function_strengthen.
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
    get_invariant _bpf_ctx.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold eval_inv, correct_get_mem_region.match_res, mr_correct in c0.
    intuition eauto.
    intros.

    instantiate (1:= ModSomething). (**r TODO: right? *)
    simpl.

    eapply correct_statement_seq_body_unit.
    simpl.

    change_app_for_statement.
    normalise_post_unit.

    eapply correct_statement_call_none.
    my_reflex.
    reflexivity.
    reflexivity.
    typeclasses eauto.
    unfold correct_upd_reg.match_res. intuition.

    reflexivity.
    reflexivity.
    reflexivity. (**r TODO: should we support `upd_reg(```( *bpf_ctx).start_addr)```;` in vc_casted? *)
    reflexivity.
    reflexivity.

    unfold INV; intro H.
    correct_Forall.
    get_invariant _st.
    get_invariant _start.
    unfold correct_get_start_addr.match_res, val32_correct in c1.
    destruct c1 as (c1 & vi & Hvi_eq).
    subst.
    exists (v::(Vint (Int.repr 1))::(Vlong (Int64.repr (Int.unsigned vi)))::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p1.
    simpl.
    reflexivity.
    intros; simpl.
    unfold val64_correct, stateless, reg_correct.
    intuition eauto.
    intros.

    eapply correct_statement_seq_body_unit.
    change_app_for_statement.
    eapply correct_statement_call_none.
    my_reflex.
    reflexivity.
    reflexivity.
    typeclasses eauto.
    unfold correct_bpf_interpreter_aux.match_res. intuition.

    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.

    unfold INV; intro H.
    correct_Forall.
    get_invariant _st.
    get_invariant _fuel.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
    intros; simpl.
    intuition eauto.
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

    unfold INV; intro H.
    correct_Forall. simpl in H.
    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    intuition eauto.
    intros.

    instantiate (1:= ModSomething). (**r TODO: right? *)

    eapply correct_statement_if_body_expr. intro EXPR.
    destruct Flag.flag_eq eqn: Hflag.
    { eapply correct_statement_seq_body with (modifies1:=ModNothing).
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

      unfold INV; intro H.
      correct_Forall. simpl in H.
      get_invariant _st.
      exists (v:: (Vint (Int.repr 0))::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0; reflexivity.
      intros; simpl.
      unfold stateless, reg_correct.
      intuition eauto.
      intros.

      instantiate (1:= ModSomething). (**r TODO: right? *)

      (*
      change (eval_reg Regs.R0) with
        ((bindM (eval_reg Regs.R0) (fun res => returnM res))). *)
      eapply correct_body_Sreturn_Some.
      intros Hst H.
      simpl in H.
      get_invariant _res.
      unfold eval_inv, correct_eval_reg.match_res, val64_correct in c0.
      destruct c0 as (c0 & vl & Hvl_eq); subst.
      exists (Vlong vl).
      split.
      unfold exec_expr. rewrite p0. reflexivity.

      split.
      unfold eval_inv, match_res, val64_correct.
      intuition eauto.
      split.
      reflexivity.
      intros.
      constructor.
      reflexivity.
    }

    eapply correct_body_Sreturn_Some; eauto.
    intros.
    eexists.
    split.
    unfold exec_expr; simpl.
    reflexivity.
    split.
    unfold match_res, val64_correct, Int64.zero; simpl.
    intuition eauto.
    split.
    reflexivity.
    intros.
    constructor.
    all: try reflexivity.
    intros. simpl in H0.
    get_invariant _f.
    unfold exec_expr.
    unfold eval_inv, correct_eval_flag.match_res, flag_correct in c0.
    rewrite p0.
    rewrite c0.
    unfold Val.of_bool, CommonLib.int_of_flag, CommonLib.Z_of_flag.
    destruct x4; reflexivity.
Qed.

End Bpf_interpreter.

Existing Instance correct_function_bpf_interpreter.
