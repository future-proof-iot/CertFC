From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values AST Clight Memory Memtype Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import correct_check_mem_aux2 correct_get_mem_region correct_cmp_ptr32_nullM.

Open Scope Z_scope.


(**
Check check_mem_aux.
check_mem_aux
     : nat ->
       permission -> AST.memory_chunk -> val -> MyMemRegionsType -> M val
*)

Section Check_mem_aux.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (permission:Type); (memory_chunk:Type); (val:Type); (list memory_region: Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := check_mem_aux.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_check_mem_aux.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons pc_correct
        (DList.DCons (stateless perm_correct)
          (DList.DCons (stateless match_chunk)
            (DList.DCons (stateless valu32_correct)
              (DList.DCons (match_region_list mrs_block)
                (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => x = v /\ ((exists b ofs, x = Vptr b ofs) \/ v = Vint (Int.zero)) /\ match_state state_block mrs_block ins_block st m.

Ltac build_app_aux T :=
  match T with
  | ?F ?X => let ty := type of X in
             let r := build_app_aux F in
             constr:((mk ty X) :: r)
  | ?X    => constr:(@nil dpair)
  end.

Ltac get_function T :=
  match T with
  | ?F ?X => get_function F
  | ?X    => X
  end.

Ltac build_app T :=
  let a := build_app_aux T in
  let v := (eval simpl in (DList.of_list_dp (List.rev a))) in
  let f := get_function T in
  match type of v with
  | DList.t _ ?L =>
      change T with (app (f: arrow_type L _) v)
  end.

Ltac change_app_for_body :=
  match goal with
  | |- @correct_body _ _ ?F _ _ _ _ _ _ _ _
    => build_app F
  end.

Ltac change_app_for_statement :=
  match goal with
  | |- @correct_statement _ _ ?F _ _ _ _ _ _ _ _
    => build_app F
  end.

Lemma check_mem_aux_eq: forall n p c v l,
  check_mem_aux n p c v l =
    if Nat.eqb n 0 then returnM Vnullptr
    else bindM (get_mem_region (Nat.pred n) l) (fun cur_mr => 
          (bindM (check_mem_aux2 cur_mr p v c) (fun check_mem =>
            (bindM (cmp_ptr32_nullM check_mem) (fun is_null =>
              if is_null then check_mem_aux (Nat.pred n) p c v l
              else returnM check_mem))))).
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


  Instance correct_function3_check_mem_aux : forall a, correct_function3 p args res f fn [] false match_arg_list match_res a.
  Proof.
    intros.
    unfold args in a.
    car_cdr.
    revert c c0 c1 c2 c3.
    induction c.
    {
      intros.
      correct_function_from_body args.
      correct_body.
      repeat intro.
      unfold INV in H.
      get_invariant _st.
      get_invariant _num.
      get_invariant _perm.
      get_invariant _chunk.
      get_invariant _addr.
      get_invariant _mrs.
      unfold stateM_correct in c.
      destruct c as (Hv_eq & Hst).
      unfold stateless in c4, c5, c6, c7.
      unfold pc_correct in c4.
      destruct c4 as (Hv0_eq1 & Hv0_range & Hv0_max).
      unfold perm_correct in c5.
      unfold match_chunk, memory_chunk_to_valu32, well_chunk_Z in c6.
      unfold valu32_correct in c7.
      destruct c7 as (Hv3_eq & (vi3 & Hc2_eq)).
      unfold match_region_list in c8.
      destruct c8 as (Hv4_eq & Hmrs_eq & Hmrs_num_eq & Hmatch).
      subst.

      eexists; exists m, Events.E0.
      split.
      {
        repeat forward_star.
      }
      split.
      unfold match_res.
      unfold Vnullptr, Int.zero; simpl.
      split; [reflexivity |].
      split; [ right; reflexivity |].
      assumption.
      split;[ constructor; reflexivity | simpl; split; reflexivity].
    }

    intros.
    correct_function_from_body args.
    correct_body.
    unfold f, app.
    rewrite check_mem_aux_eq.
    eapply correct_statement_if_body_expr.
    simpl.
    apply correct_statement_seq_set with (match_res1 := fun _ => pc_correct c).
    +
      intros.
      unfold INV in H.
      get_invariant _st.
      get_invariant _num.
      get_invariant _perm.
      get_invariant _chunk.
      get_invariant _addr.
      get_invariant _mrs.
      unfold stateM_correct in c4.
      destruct c4 as (Hv_eq & Hst).
      unfold stateless in c5, c6, c7, c8.
      unfold pc_correct in c5.
      destruct c5 as (Hv0_eq1 & Hv0_range & Hv0_max).
      unfold perm_correct in c6.
      unfold match_chunk, memory_chunk_to_valu32, well_chunk_Z in c7.
      unfold valu32_correct in c8.
      destruct c8 as (Hv3_eq & (vi3 & Hc2_eq)).
      unfold match_region_list in c9.
      destruct c9 as (Hv4_eq & Hmrs_eq & Hmrs_num_eq & Hmatch).
      subst.
      eexists.
      split.
      {
        unfold exec_expr.
        rewrite p1.
        unfold Cop.sem_binary_operation, Cop.sem_sub; simpl.
        unfold Cop.sem_binarith; simpl.
        unfold Int.sub.
        fold Int.one; rewrite Int.unsigned_one.
        rewrite Zpos_P_of_succ_nat.
        rewrite <- Nat2Z.inj_succ.
        change Ptrofs.max_unsigned with 4294967295 in Hv0_max.
        rewrite Int.unsigned_repr; [ | change Int.max_unsigned with 4294967295; lia].
        rewrite Nat2Z.inj_succ.
        rewrite <- Z.add_1_r.
        rewrite Z.add_simpl_r.
        reflexivity. (**r all above operations is to simplfy the result*)
      }
      split.
      {
        unfold pc_correct.
        split; [reflexivity| ].
        split; [| assumption].
        lia.
      }
    constructor.
    simpl.
    reflexivity.
  +
    unfold INV.
    simpl. intuition subst ; discriminate.
  + (**r then here we lose m0 = m? *)
    intros.
    (**r correct_body _ _ (bindM (get_mem_region _ _) ... *)
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

Ltac prove_in_inv :=
  simpl; intuition subst; discriminate.
    prove_in_inv.
    prove_in_inv.
    reflexivity.
    reflexivity.

    unfold INV; intro H.
    correct_Forall.
    get_invariant _n.
    get_invariant _mrs.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1; reflexivity.
    simpl;intros.
    intuition eauto.

    intros.
    (**r goal: correct_body p val (bindM (check_mem_aux2 ... *)
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
    exists (v::v0::v1::v2::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3; reflexivity.
    simpl;intros.
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
    get_invariant _check_mem.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1; reflexivity.
    simpl;intros.
    intuition eauto.

    intros.
    eapply correct_statement_if_body; [prove_in_inv | destruct x2 ]. 2:{
      unfold correct_body, returnM.
      intros.
      unfold INV in H.
      get_invariant _st.
      get_invariant _check_mem.
      unfold stateM_correct in c4.
      destruct c4 as (Hv_eq & Hst).
      unfold correct_check_mem_aux2.match_res in c5.
      destruct c5 as (Hv0_eq & Hc5_eq); subst.
      instantiate (1 := nil).
      destruct Hc5_eq as [ (b & ofs & Hptr) | Hnull].
      - rewrite Hptr.
        eexists; exists m3, Events.E0.
        split.
        forward_star.
        unfold Cop.sem_cast; simpl.
        rewrite Hptr.
        reflexivity.
        forward_star.
        split.
        unfold match_res.
        rewrite Hptr.
        split; [reflexivity | ].
        split; [left; eexists; eexists; reflexivity | assumption].
        split; [rewrite Hptr; constructor; reflexivity | split; reflexivity].
      - rewrite Hnull.
        eexists; exists m3, Events.E0.
        split.
        forward_star.
        rewrite Hnull.
        reflexivity.
        rewrite Hnull.
        forward_star.
        rewrite Hnull.
        split.
        unfold match_res.
        split; [reflexivity | ].
        split; [right; reflexivity | assumption].
        split; [constructor; reflexivity | split; reflexivity].
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
    unfold stateM_correct in c4.
    destruct c4 as (Hv_eq & Hst).
    unfold pc_correct in c5.
    destruct c5 as (Hv0_eq & Hc_range & Hc_max).
    unfold stateless, perm_correct in c6.
    unfold stateless, match_chunk in c7.
    unfold stateless, valu32_correct in c8.
    destruct c8 as (Hv3_eq & vi & Hvi_eq).
    subst.
    exists ((Vptr state_block Ptrofs.zero) ::
            (Vint (Int.repr (Z.of_nat c))) ::
            v1 ::
            (memory_chunk_to_valu32 c1) ::
            (Vint vi) ::
            v4::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0, p1, p2, p3, p4, p5; reflexivity.
    simpl;intros.
    unfold stateM_correct, pc_correct, stateless, perm_correct, match_chunk, valu32_correct.
    intuition eauto.
    reflexivity.
  +
    reflexivity.
  + intro.
    unfold INV in H.
    get_invariant _num.
    unfold pc_correct in c4.
    destruct c4 as (Hv_eq & Hrange & Hmax).
    unfold exec_expr.
    rewrite p0.
    simpl.
    rewrite <- Hv_eq.
    unfold Cop.sem_cmp, Cop.sem_binarith, Val.of_bool, Vfalse; simpl.
    unfold Int.eq.
    change (Int.unsigned (Int.repr 0)) with 0.
    change Ptrofs.max_unsigned with Int.max_unsigned in Hmax.
    rewrite Nat2Z.inj_succ in Hrange.
    rewrite Zpos_P_of_succ_nat.
    rewrite Int.unsigned_repr;[ | lia].
    assert (Hneq: (Z.succ (Z.of_nat c)) <> 0). {
      lia.
    }
    eapply zeq_false in Hneq.
    rewrite Hneq.
    reflexivity.
Qed.

End Check_mem_aux.

Close Scope Z_scope.

Existing Instance correct_function3_check_mem_aux.
