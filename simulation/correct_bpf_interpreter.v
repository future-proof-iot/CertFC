From bpf.comm Require Import MemRegion State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From dx.Type Require Import Bool.
From dx Require Import IR.
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

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := bpf_interpreter.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Variable modifies : list block. (* of the C code *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_interpreter.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (stateless nat_correct_overflow)
            (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v /\ match_state state_block mrs_block ins_block st m.

  Instance correct_function3_bpf_interpreter : forall a, correct_function3 p args res f fn (state_block::modifies) false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app.
    unfold bpf_interpreter.

    eapply correct_statement_seq_body with (modifies1:=nil).
    change_app_for_statement.
    eapply correct_statement_call with (has_cast := false).

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
      intuition. subst m' st'. assumption.
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

    eapply correct_statement_seq_body with (modifies1:=nil).
    change_app_for_statement.
    eapply correct_statement_call with (has_cast := false).

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
      destruct H as (Hm_eq & Hst_eq); subst.
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
    get_invariant _mrs.
    exists ((Vint (Int.repr 0))::v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold correct_eval_mrs_regions.match_res in c0.
    unfold stateless, nat_correct.
    intuition eauto.
    intros.

    eapply correct_statement_seq_body with (modifies1:=[state_block]).
    change_app_for_statement.
    instantiate (3:= (fun _ v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef)).
    instantiate (2:= _upd_reg).
    instantiate (1:= (Ctypes.Tfunction
           (Ctypes.Tcons
              (Clightdefs.tptr (Ctypes.Tstruct _bpf_state Ctypes.noattr))
              (Ctypes.Tcons Clightdefs.tuint
                 (Ctypes.Tcons Clightdefs.tulong Ctypes.Tnil))) Clightdefs.tvoid
           cc_default)).
    admit. (*
    eapply correct_statement_call_none.

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
      destruct H as (Hm_eq & Hst_eq); subst.
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
    get_invariant _mrs.
    exists ((Vint (Int.repr 0))::v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0; reflexivity.
    intros; simpl.
    unfold correct_eval_mrs_regions.match_res in c0.
    unfold stateless, nat_correct.
    intuition eauto. *)

    intros.

    eapply correct_statement_seq_body with (modifies1:=(state_block::modifies)).
    change_app_for_statement.
    instantiate (3:= (fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef)).
    instantiate (2:= _bpf_interpreter_aux).
    instantiate (1:= (Ctypes.Tfunction
           (Ctypes.Tcons
              (Clightdefs.tptr (Ctypes.Tstruct _bpf_state Ctypes.noattr))
              (Ctypes.Tcons Clightdefs.tuint Ctypes.Tnil)) Clightdefs.tvoid
           cc_default)).
    admit. (*
    eapply correct_statement_call_none. *)

    intros.

    eapply correct_statement_seq_body with (modifies1:=nil).
    change_app_for_statement.
    eapply correct_statement_call with (has_cast := false).

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
      destruct H as (Hm_eq & Hst_eq); subst.
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

    eapply correct_statement_if_body_expr. intro EXPR.
    destruct Flag.flag_eq eqn: Hflag.
    {
      unfold match_res. admit. (*
      eapply correct_statement_seq_body with (modifies1:=nil).
      (**r ?M4958 v' v st' m' <> match_res (State.eval_reg Regs.R0 st4) v st4 m' *)
      eapply correct_body_call_ret with (has_cast := false).
      change_app_for_statement.
      eapply correct_statement_call with (has_cast := false).

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
        destruct H as (Hm_eq & Hst_eq); subst.
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
      intros. *)
    }

    eapply correct_body_Sreturn_Some; eauto.
    intros.
    split.
    unfold exec_expr; simpl.
    reflexivity.
    split.
    unfold match_res, val64_correct, Int64.zero; simpl.
    get_invariant _st.
    unfold stateM_correct in c0.
    destruct c0 as (_ & Hst).
    intuition eauto.
    all: try reflexivity.
    intros.
    get_invariant _f.
    unfold exec_expr.
    unfold correct_eval_flag.match_res, flag_correct in c0.
    rewrite p0.
    rewrite c0.
    unfold Val.of_bool, CommonLib.int_of_flag, CommonLib.Z_of_flag.
    destruct x3; reflexivity. 
    admit.
    (*
    instantiate (1:=nil).
    reflexivity. *)
Admitted.

End Bpf_interpreter.

Existing Instance correct_function3_bpf_interpreter.