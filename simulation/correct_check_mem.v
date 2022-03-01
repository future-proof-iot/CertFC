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

From bpf.simulation Require Import correct_is_well_chunk_bool correct_eval_mrs_num correct_eval_mrs_regions correct_check_mem_aux correct_cmp_ptr32_nullM.

(**
Check check_mem.
check_mem
     : permission -> memory_chunk -> val -> M val
*)

Section Check_mem.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(permission:Type); (memory_chunk:Type); (val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := check_mem.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_check_mem.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons (stateless perm_correct)
        (DList.DCons (stateless match_chunk)
          (DList.DCons (stateless valu32_correct)
            (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => (val_ptr_null_block_correct state_block mrs_block ins_block x v st m) /\ match_state state_block mrs_block ins_block st m.

  Instance correct_function3_check_mem : forall a, correct_function3 p args res f fn (nil) false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app.
    unfold check_mem.
    eapply correct_statement_seq_body with (modifies1:=nil).
    change_app_for_statement.
    eapply correct_statement_call with (has_cast := true).

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
    change (match_temp_env INV le st m) in H.
    unfold INV in H.
    get_invariant _chunk.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0.
    reflexivity.
    intros; simpl.
    intuition eauto.

    intros.
    eapply correct_statement_if_body; [prove_in_inv | destruct x ]. 2:{ (**r if-else branch *)
      unfold correct_body.
      instantiate (1 := nil).
      intros.
      unfold returnM.
      intros.
      exists (Vint (Int.repr 0)), m0, Events.E0.
      split.
      {
        forward_star.
        forward_star.
      }
      split.
      {
        unfold match_res, val_ptr_null_block_correct, Vnullptr, Int.zero; simpl.
        split; [split; [reflexivity |] | ].
        right.
        reflexivity.
        get_invariant _st.
        unfold stateM_correct in c2.
        destruct c2 as (_ & c2); assumption.
      }
      split;[ constructor; reflexivity | ].
      split; reflexivity.
    }
    (**r if-then branch *)

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
    unfold map_opt,exec_expr.
    rewrite p0; reflexivity.
    simpl; intros.
    instantiate (1 := ins_block).
    instantiate (1 := mrs_block).
    instantiate (1 := state_block).
    unfold correct_eval_mrs_num.stateM_correct.
    unfold stateM_correct in c2.
    destruct c2 as (Hc2_eq & Hst); subst.
    split; [| constructor].
    split; [ reflexivity | assumption ].

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
    unfold stateM_correct in c2.
    destruct c2 as (Hc2_eq & Hst); subst.
    exists (Vptr state_block Ptrofs.zero::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    instantiate (1 := ins_block).
    instantiate (1 := mrs_block).
    instantiate (1 := state_block).
    unfold correct_eval_mrs_num.stateM_correct.
    split; [| constructor].
    split; [ reflexivity | assumption ].

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
    get_invariant _mem_reg_num.
    get_invariant _perm.
    get_invariant _chunk.
    get_invariant _addr.
    get_invariant _mrs.
    exists (v :: v0 :: v1 :: v2 :: v3 :: v4 :: nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3, p4, p5; reflexivity.
    simpl;intros.
    instantiate (1 := ins_block).
    instantiate (1 := mrs_block).
    instantiate (1 := state_block).
    unfold correct_check_mem_aux.stateM_correct.
    unfold stateM_correct in c2.
    destruct c2 as (Hv_eq & Hst).
    unfold correct_eval_mrs_num.match_res in c3.
    destruct c3 as (Hc_eq & _).
    unfold correct_eval_mrs_regions.match_res in c7.
    destruct c7 as (Hx0_eq & Hmrs & _).
    intuition eauto.

    intros.
    eapply correct_statement_seq_body with (modifies1:=nil);eauto.
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
    get_invariant _st.
    get_invariant _check_mem__1.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1; reflexivity.
    simpl;intros.
    unfold correct_cmp_ptr32_nullM.stateM_correct, stateless, val_ptr_null_block_correct.
    unfold correct_check_mem_aux.match_res, val_ptr_null_block_correct in c3.
    destruct c3 as ((Hv0_eq & Hptr) & Hst).
    unfold stateM_correct in c2.
    subst.
    intuition eauto.

    intros.
    eapply correct_statement_if_body; [prove_in_inv | destruct x2 ]. 2:{
      unfold correct_body, returnM.
      intros.
      unfold INV in H.
      get_invariant _check_mem__1.
      unfold correct_check_mem_aux.match_res, val_ptr_null_block_correct in c2.
      destruct c2 as ((Hv_eq & Hptr) & Hst).
      subst.
      exists v, m4, Events.E0.
      instantiate (1 := nil).
      destruct Hptr as [ (b & ofs & Hvalid_blk & Hptr & Hinvalid) | Hnull].
      - rewrite Hptr.
        split.
        forward_star.
        unfold Cop.sem_cast; simpl.
        rewrite Hptr.
        reflexivity.
        rewrite Hptr.
        forward_star.
        split.
        unfold match_res, val_ptr_null_block_correct.
        split; [split; [reflexivity | ] | assumption].
        left; exists b; eexists; split; [assumption | split; [reflexivity | assumption]].
        split; [constructor; reflexivity | split; reflexivity].
      - rewrite Hnull.
        split.
        forward_star.
        rewrite Hnull.
        reflexivity.
        rewrite Hnull.
        forward_star.
        split.
        unfold match_res, val_ptr_null_block_correct.
        split; [split; [reflexivity |] | assumption].
        right; reflexivity.
        split; [constructor; reflexivity | split; reflexivity].
    }
    eapply correct_body_Sreturn_Some; eauto.
    intros.
    split.
    unfold exec_expr; simpl.
    reflexivity.
    split.
    unfold match_res, val_ptr_null_block_correct, Vnullptr, Int.zero; simpl.
    split; [split; [reflexivity |] |].
    right; reflexivity.
    get_invariant _st.
    unfold stateM_correct in c2.
    destruct c2 as (_ & Hst).
    assumption.
    reflexivity.

    intuition.
    all: reflexivity.
  Qed.

End Check_mem.

Existing Instance correct_function3_check_mem.