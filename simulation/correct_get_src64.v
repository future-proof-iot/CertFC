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

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_src64.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_src64.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons (stateless opcode_correct)
        (DList.DCons (stateless ins64_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v.

  Instance correct_function3_get_src64 : forall a, correct_function3 p args res f fn (nil) false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app, get_src64.
    intros.

    eapply correct_statement_if_body_expr. intro EXPR.
    destruct Int.eq eqn: Heq.
    - eapply correct_statement_seq_body with (modifies1:=nil).
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
      instantiate (1 := nil).
      eapply correct_body_Sreturn_Some; eauto.
      intros.
      get_invariant _imm64.
      unfold correct_eval_immediate.match_res, val64_correct in c1.
      destruct c1 as (Hv_eq & vl & Hvl_eq).
      subst.
      split.
      unfold exec_expr, empty_env.
      rewrite p0. reflexivity.
      split.
      unfold match_res, val64_correct; simpl.
      split; [reflexivity | eexists; reflexivity].
      reflexivity.
      instantiate (1 := nil).
      all: reflexivity.
    - eapply correct_statement_seq_body with (modifies1:=nil).
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

      intros.
      correct_Forall.
      get_invariant _ins.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      intros; simpl.
      unfold ins64_correct.
      tauto.

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
        intuition. subst m' st'. assumption.
      }

      reflexivity.
      reflexivity.
      reflexivity.
      prove_in_inv.
      prove_in_inv.
      reflexivity.
      reflexivity.

      intros.
      correct_Forall.
      get_invariant _st.
      get_invariant _src.
      exists (v::v0::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0, p1.
      reflexivity.
      intros; simpl.
      instantiate (1 := ins_block).
      instantiate (1 := mrs_block).
      instantiate (1 := state_block).
      unfold correct_get_src.match_res in c2.
      unfold correct_eval_reg.stateM_correct, stateless.
      unfold stateM_correct in c1.
      tauto.

      intros.
      instantiate (1 := nil).
      eapply correct_body_Sreturn_Some; eauto.
      intros.
      get_invariant _src64.
      unfold correct_eval_reg.match_res, val64_correct in c1.
      destruct c1 as (Hv_eq & vl & Hvl_eq).
      subst.
      split.
      unfold exec_expr, empty_env.
      rewrite p0; reflexivity.
      split.
      unfold match_res, val64_correct; simpl.
      split; [reflexivity | eexists; reflexivity].
      reflexivity.
      instantiate (1 := nil).
      all: reflexivity.
    - reflexivity.
    - intro.
      get_invariant _x.
      unfold exec_expr.
      rewrite p0.
      simpl.
      unfold stateless, opcode_correct in c1.
      destruct c1 as (Hv_eq & Hc_le); subst.
      unfold Cop.sem_and, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
      reflexivity. (*
      unfold Int.eq, Int.and.
      assert (Hz: 0 <= Z.of_nat c <= 255) by lia.
      rewrite Int.unsigned_repr with (z:= Z.of_nat c); [| change Int.max_unsigned with 4294967295; lia].
      change (Int.unsigned (Int.repr 0)) with 0.
      change (Int.unsigned (Int.repr 8)) with 8. *)
      (**r I don't want to prove Z.land (Z.of_nat c) 8 = Z.of_nat(Nat.land c 8), so I modify the definition of `rBPFInterpreter.v/get_src64` *)
  Qed.

End Get_src64.
Close Scope Z_scope.

Existing Instance correct_function3_get_src64.
