From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import correct_is_well_chunk_bool correct_get_sub correct_get_add correct_get_start_addr correct_get_block_size correct_get_block_perm. (**r correct_get_block_ptr *)

Open Scope Z_scope.

Section Check_mem_aux2.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition args  := [(memory_region:Type) ; (permission:Type); val; (AST.memory_chunk: Type)].
Definition res  := val.

(* [f] is a Coq Monadic function with the right type *)
Definition f := check_mem_aux2.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_check_mem_aux2.

Definition is_vlong (v: val) :=
  match v with
  | Vlong _ => True
  | _       => False
  end.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

Definition match_arg  :
  DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
  DList.DCons
    (match_region mrs_block)
    (DList.DCons
        (stateless perm_correct)
        (DList.DCons
           (stateless valu32_correct)
           (DList.DCons (stateless match_chunk)
                        (DList.DNil _)))).

Definition match_res (v1 :val) (v2:val) (st: State.state) (m: Mem.mem) :=
  v1 = v2 /\ ((exists b ofs, v1 = Vptr b ofs) \/ v1 = Vint (Int.zero)).


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

Ltac prove_incl :=
  simpl; unfold incl; simpl; intuition congruence.

Ltac prove_in_inv :=
  simpl; intuition subst; discriminate.

Lemma correct_function_check_mem_aux2_correct : forall a, correct_function3 p args res f fn (nil) true match_arg match_res a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f. unfold check_mem_aux2.
  simpl.
  (** goal: correct_body _ _ (bindM (is_well_chunk_bool ... *)
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
    intuition. clear - H2 H.
    unfold match_elt in *;
      unfold fst in *.
    destruct (Maps.PTree.get _mr le);auto.
    simpl in *.
    destruct H2 ; split; auto.
    unfold match_region in *.
    all: destruct H; auto.
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
  unfold map_opt. unfold exec_expr. rewrite p0.
  reflexivity.
  intros. simpl.
  tauto.

  intros.
  (** goal: correct_body _ _ (if x then ... *)
  eapply correct_statement_if_body; [prove_in_inv | destruct x ]. 2:{ (**r if-else branch *)
  unfold correct_body.
  intros.
  unfold returnM.
  intros.
  exists (Vint (Int.repr 0)), m0, Events.E0. 
  repeat split.

  forward_star.
  forward_star.
  intuition.
  constructor.
  reflexivity.
  instantiate (1 := nil).
  split; reflexivity.
  }
  (**r if-then branch *)

  (** goal: correct_body _ _ (bindM (get_start_addr c) ... *)
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
  get_invariant _mr.
  exists (v::nil).
  split.
  unfold map_opt,exec_expr.
  rewrite p0.
  reflexivity.
  simpl. intros.
  intuition eauto.
  intros.
  (** goal: correct_body _ _ (bindM (get_block_size c) ... *)
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
  get_invariant _mr.
  (**  exists lval : list val, _ [Etempvar _mr3 _] = Some lval *)
  exists (v::nil).
  split.
  unfold map_opt, exec_expr.
  rewrite p0; reflexivity.
  simpl;intros.
  intuition eauto.
  intros.
  (**r goal: correct_body p val (bindM (get_block_perm c) ... *)
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
  get_invariant _mr.
  (**  exists lval : list val, _ [Etempvar _mr3 _] = Some lval *)
  exists (v::nil).
  split.
  unfold map_opt, exec_expr.
  rewrite p0; reflexivity.
  simpl;intros.
  intuition eauto.
  intros.


  (** goal:  correct_body _ _ (bindM (get_sub c0 x0) ... *)
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
  get_invariant _addr.
  get_invariant _start.
  (**  exists lval : list val, _ [(Etempvar _addr0 _); (Etempvar _start _)] = Some lval *)
  exists ([v; v0]).
  split.
  unfold map_opt, exec_expr.
  rewrite p0, p1; reflexivity.
  simpl;intros.
  intuition; eauto.
  eauto.
  intros.
  (** goal:  correct_body _ _ (bindM (get_add x2 (memory_chunk_to_valu32 c1)) ... *)
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
  get_invariant _lo_ofs.
  get_invariant _chunk.
  unfold map_opt, exec_expr.
  rewrite p0, p1.
  exists ([v; v0]).
  split.
  unfold map_opt, exec_expr. reflexivity.
  simpl;intros.
  intuition eauto.

  unfold stateless, valu32_correct, memory_chunk_to_valu32, well_chunk_Z.
  unfold stateless, match_chunk, memory_chunk_to_valu32, well_chunk_Z in c4.
  intuition eauto.
  intros.

  (**r then we consider the `if-then` case *)

Ltac destruct_if Hname :=
  match goal with
  | |- context[(if ?X then _ else _)] =>
    destruct X eqn: Hname
  end.
  destruct_if Hcond.
  (**r we have two goals: 
    1. if-Hcond-then
    2. if-Hcond-else
    *)
  2:{
    unfold list_rel_arg,app;
    match goal with
    |- correct_body _ _ _ _ ?B _ ?INV
                 _ _ _ _ =>
      let I := fresh "INV" in
      set (I := INV) ; simpl in I;
      let B1 := eval simpl in B in
        change B with B1
    end.
    unfold correct_body.
    unfold returnM.
    intros.

    unfold INV0, INV in H.
    get_invariant _hi_ofs.
    get_invariant _lo_ofs.
    get_invariant _size.
    get_invariant _chunk.
    get_invariant _mr_perm.
    get_invariant _perm.
    unfold correct_get_add.match_res, valu32_correct in c3.
    destruct c3 as (H0_eq & (vi0 & Hvi0_eq)).
    unfold correct_get_sub.match_res, valu32_correct in c4.
    destruct c4 as (H2_eq & (vi2 & Hvi2_eq)).
    unfold correct_get_block_size.match_res, valu32_correct in c5.
    destruct c5 as (H4_eq & (vi4 & Hvi4_eq)).
    unfold stateless, match_chunk, memory_chunk_to_valu32 in c6.
    unfold correct_get_block_perm.match_res, perm_correct in c7.
    unfold stateless, perm_correct in c8.
    subst.


    (**r we also need those info below *)
    assert (Hneq1: _lo_ofs <> _t'7). {
      unfold _lo_ofs, _t'7.
      intro Hneq; inversion Hneq.
    }
    assert (Hneq2: _chunk <> _t'8). {
      unfold _chunk, _t'8.
      intro Hneq; inversion Hneq.
    }
    assert (Hwell_chunk_unsigned: Int.unsigned (Int.repr (well_chunk_Z c2)) = well_chunk_Z c2). {
      destruct c2; simpl; try (fold Int.zero; apply Int.unsigned_zero); try rewrite Int.unsigned_repr; try reflexivity; try rewrite Int_max_unsigned_eq64; try lia.
    }

    assert (Hchunk_ne_zero: Int.eq (Int.repr (well_chunk_Z c2)) Int.zero = false). {
      unfold Int.zero.
      destruct c2; unfold Int.eq; simpl;
      repeat rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try apply zeq_false; try lia.
    }

    exists (Vint Int.zero), m5, Events.E0.
    repeat split.

    unfold compu_lt_32, compu_le_32, compu_le_32, val32_modu, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound in Hcond.
    change Int.max_unsigned with 4294967295 in Hcond.
    - destruct (Int.ltu _ _) eqn: Hltu.
      + rewrite andb_true_l in Hcond.
        destruct (negb (Int.ltu (Int.repr (_ - well_chunk_Z _)) _)) eqn: Hle.
      * rewrite andb_true_l in Hcond.
        unfold Val.modu in Hcond.
        rewrite Hchunk_ne_zero in Hcond.
        destruct (Int.eq Int.zero (Int.modu _ _)) eqn: Hmod.
        {
          rewrite andb_true_l in Hcond.
          do 4 forward_star.
          simpl.
          rewrite Hltu.
          simpl.
          unfold Cop.bool_val, Vtrue; simpl.
          rewrite Int_eq_one_zero.
          unfold negb.
          reflexivity.
          simpl.
          unfold step2; forward_star.
          simpl.
          unfold Int.sub. fold Int.mone. rewrite Int.unsigned_mone.
          change (Int.modulus - 1) with 4294967295.
          rewrite Hwell_chunk_unsigned.
          rewrite Hle.
          simpl.
          unfold Cop.bool_val, Vtrue; simpl.
          rewrite Int_eq_one_zero.
          unfold negb.
          reflexivity.
          simpl.
          unfold step2; forward_star.
          forward_star.
          simpl.
          unfold Cop.sem_mod, Cop.sem_binarith; simpl.
          rewrite Hchunk_ne_zero.
          reflexivity.
          simpl.
          unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
          fold Int.zero.
          rewrite Hmod.
          simpl.
          unfold Vtrue.
          reflexivity.
          simpl.
          unfold Cop.sem_cast; simpl.
          rewrite Int_eq_one_zero.
          reflexivity.
          do 4 forward_star. forward_star.
          post_process.
          post_process.
          simpl.
          unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
          unfold Cop.sem_cast; simpl.
          unfold rBPFMemType.perm_ge in Hcond.
          destruct c0 eqn: Hc0_eq; destruct x1 eqn: Hx1_eq; inversion Hcond; rewrite c7, c8; unfold Int.ltu; repeat rewrite Int_unsigned_repr_n; try reflexivity; try lia; simpl in Hcond; inversion Hcond.
          simpl.
          unfold Cop.sem_cast, Vfalse; simpl.
          rewrite Int.eq_true.
          reflexivity.
          do 4 forward_star. forward_star.
        }

        do 4 forward_star.
        simpl.
        rewrite Hltu.
        unfold Cop.bool_val, Val.of_bool; simpl.
        rewrite Int_eq_one_zero.
        unfold negb; reflexivity.
        simpl.
        unfold step2; forward_star.
        simpl.
        unfold Int.sub. fold Int.mone. rewrite Int.unsigned_mone.
        change (Int.modulus - 1) with 4294967295.
        rewrite Hwell_chunk_unsigned.
        rewrite Hle.
        simpl.
        unfold Cop.bool_val, Vtrue; simpl.
        rewrite Int_eq_one_zero.
        unfold negb.
        reflexivity.
        simpl.
        unfold step2; forward_star.
        forward_star.
        simpl.
        unfold Cop.sem_mod, Cop.sem_binarith; simpl.
        rewrite Hchunk_ne_zero.
        reflexivity.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        fold Int.zero.
        rewrite Hmod.
        simpl.
        unfold Vtrue.
        reflexivity.
        simpl.
        unfold Cop.sem_cast, Vfalse; simpl.
        rewrite Int.eq_true.
        reflexivity.
        do 4 forward_star.
        do 4 forward_star.
        fold Int.zero; forward_star.
        forward_star.
        forward_star.
      * do 4 forward_star.
        simpl.
        rewrite Hltu.
        unfold Cop.bool_val, Val.of_bool; simpl.
        rewrite Int_eq_one_zero.
        unfold negb; reflexivity.
        simpl.
        unfold step2; forward_star.
        simpl.
        unfold Int.sub. fold Int.mone. rewrite Int.unsigned_mone.
        change (Int.modulus - 1) with 4294967295.
        rewrite Hwell_chunk_unsigned.
        rewrite Hle.
        simpl.
        unfold Cop.bool_val, Vfalse; simpl.
        rewrite Int.eq_true.
        unfold negb.
        reflexivity.
        simpl.
        unfold step2; forward_star.
        forward_star. forward_star.
        fold Int.zero.
        do 2 rewrite Int.eq_true.
        unfold negb.
        do 4 forward_star. forward_star. forward_star.
      + do 4 forward_star.
        simpl.
        rewrite Hltu.
        unfold Cop.bool_val, Val.of_bool; simpl.
        rewrite Int.eq_true.
        unfold negb; reflexivity.
        simpl.
        unfold step2; forward_star.
        do 4 forward_star.
        fold Int.zero.
        rewrite Int.eq_true.
        unfold negb.
        do 4 forward_star.
        do 4 forward_star.
        do 4 forward_star.
        forward_star.
    - right; unfold Vnullptr; simpl; reflexivity.
    - constructor; reflexivity.
    - instantiate (1 := nil).
      split; reflexivity.
  }

  (**r if-Hcond-then *)
  unfold list_rel_arg,app;
  match goal with
  |- correct_body _ _ _ _ ?B _ ?INV
               _ _ _ _ =>
    let I := fresh "INV" in
    set (I := INV) ; simpl in I;
    let B1 := eval simpl in B in
      change B with B1
  end.
  unfold correct_body.
  unfold returnM.
  intros.

  unfold INV0, INV in H.
  get_invariant _hi_ofs.
  get_invariant _lo_ofs.
  get_invariant _size.
  get_invariant _chunk.
  get_invariant _perm.
  get_invariant _mr_perm.
  get_invariant _mr.

  unfold correct_get_add.match_res, valu32_correct in c3.
  destruct c3 as (H0_eq & (vi0 & Hvi0_eq)).
  unfold correct_get_sub.match_res, valu32_correct in c4.
  destruct c4 as (H2_eq & (vi2 & Hvi2_eq)).
  unfold correct_get_block_size.match_res, valu32_correct in c5.
  destruct c5 as (H4_eq & (vi4 & Hvi4_eq)).
  unfold stateless, match_chunk, memory_chunk_to_valu32 in c6.
  unfold stateless, perm_correct in c7.
  unfold correct_get_block_perm.match_res, perm_correct in c8.
  unfold match_region, match_region_at_ofs in c9.
  destruct c9 as (ofs & Hv5_eq & ((Hvl_start_addr & Hstart_addr & Hstart_addr_eq) & (Hvl_block_size & Hblock_size & Hblock_size_eq) & (Hvl_block_perm & Hblock_perm & Hblock_perm_eq) & (Hb_block_ptr & Hblock_ptr & Hblock_ptr_eq))).
  subst.

  (**r we also need those info below *)
  assert (Hneq1: _lo_ofs <> _t'7). {
    unfold _lo_ofs, _t'7.
    intro Hneq; inversion Hneq.
  }
  assert (Hneq2: _chunk <> _t'8). {
    unfold _chunk, _t'8.
    intro Hneq; inversion Hneq.
  }
  assert (Hwell_chunk_unsigned: Int.unsigned (Int.repr (well_chunk_Z c2)) = well_chunk_Z c2). {
    destruct c2; simpl; try (fold Int.zero; apply Int.unsigned_zero); try rewrite Int.unsigned_repr; try reflexivity; try rewrite Int_max_unsigned_eq64; try lia.
  }

  assert (Hchunk_ne_zero: Int.eq (Int.repr (well_chunk_Z c2)) Int.zero = false). {
    unfold Int.zero.
    destruct c2; unfold Int.eq; simpl;
    repeat rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try apply zeq_false; try lia.
  }


  unfold compu_lt_32, compu_le_32, compu_le_32, val32_modu, memory_chunk_to_valu32, memory_chunk_to_valu32_upbound in Hcond.
  change Int.max_unsigned with 4294967295 in Hcond.
  repeat rewrite andb_true_iff in Hcond.
  destruct Hcond as ((Hltu & Hle & Hmod) & Hperm).
  unfold Val.modu in Hmod.
  rewrite Hchunk_ne_zero in Hmod.

  eexists; exists m5, Events.E0.
  repeat split.
  do 4 forward_star.
  simpl.
  rewrite Hltu.
  unfold Val.of_bool.
  unfold Cop.bool_val, Vtrue; simpl.
  rewrite Int_eq_one_zero.
  unfold negb.
  reflexivity.
  simpl.
  unfold step2; forward_star.
  forward_star.
  simpl.
  unfold Cop.sem_mod, Cop.sem_binarith; simpl.
  unfold Int.sub. fold Int.mone. rewrite Int.unsigned_mone.
  change (Int.modulus - 1) with 4294967295.
  rewrite Hwell_chunk_unsigned.
  rewrite Hle.
  simpl.
  unfold Cop.bool_val, Vtrue; simpl.
  rewrite Int_eq_one_zero.
  unfold negb.
  reflexivity.
  simpl.
  unfold step2; forward_star.
  forward_star.
  simpl.
  unfold Cop.sem_mod, Cop.sem_binarith; simpl.
  rewrite Hchunk_ne_zero.
  reflexivity.
  simpl.
  unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
  fold Int.zero.
  rewrite Hmod.
  simpl.
  unfold Vtrue.
  reflexivity.
  simpl.
  unfold Cop.sem_cast; simpl.
  rewrite Int_eq_one_zero.
  reflexivity.
  do 4 forward_star.
  forward_star.
  post_process.
  post_process.
  unfold Cop.sem_binary_operation; simpl.
  unfold Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
  unfold rBPFMemType.perm_ge in Hperm.
  destruct c0, x1; unfold Int.ltu; rewrite c7, c8; repeat rewrite Int_unsigned_repr_n; try reflexivity; try lia; simpl in Hperm; inversion Hperm.
  unfold Cop.sem_cast; simpl.
  rewrite Int_eq_one_zero.
  reflexivity.
  do 4 forward_star.
  post_process.
  unfold align, Ctypes.alignof; simpl.
  apply Hblock_ptr.
  try post_process.
  reflexivity.
  simpl.
  rewrite Hblock_ptr_eq.
  unfold Val.add.
  simpl.
  fold Ptrofs.one.
  rewrite Ptrofs.mul_commut.
  rewrite Ptrofs.mul_one.
  forward_star.
  forward_star.

  left.
  eexists; eexists.
  unfold Val.add; simpl; rewrite Hblock_ptr_eq; reflexivity.
  rewrite Hblock_ptr_eq.
  unfold Val.add.
  simpl.
  constructor.
  all: try reflexivity.

Qed.

End Check_mem_aux2.

Close Scope Z_scope.

Existing Instance correct_function_check_mem_aux2_correct.
(*  *)