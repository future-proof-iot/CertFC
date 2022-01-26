From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values AST Clight Memory Memtype Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.simulation Require Import correct_check_mem_aux2 correct_get_mem_region.

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
      (DList.DCons (stateless nat_correct)
        (DList.DCons (stateless perm_correct)
          (DList.DCons (stateless match_chunk)
            (DList.DCons (stateless valu32_correct)
              (DList.DCons (match_region_list mrs_block)
                (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => x = v /\ ((exists b ofs, x = Vptr b ofs) \/ v = Vint (Int.zero)) /\ match_state state_block mrs_block ins_block st m.

  Instance correct_function3_check_mem_aux : forall a, correct_function3 p args res f fn [] false match_arg_list match_res a.
  Proof.
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
    unfold stateM_correct in c4.
    destruct c4 as (Hv_eq & Hst).
    unfold stateless in c5, c6, c7, c8.
    unfold nat_correct in c5.
    destruct c5 as (Hv0_eq1 & Hv0_range).
    unfold perm_correct in c6.
    unfold match_chunk, memory_chunk_to_valu32, well_chunk_Z in c7.
    unfold valu32_correct in c8.
    destruct c8 as (Hv3_eq & (vi3 & Hc2_eq)).
    unfold match_region_list in c9.
    destruct c9 as (Hv4_eq & Hmrs_eq & Hmrs_num_eq & Hmatch).
    subst.


    unfold f. unfold check_mem_aux.
    simpl.
    TBC...
  (** goal: correct_body _ _ (bindM (is_well_chunk_bool ... *)
  correct_forward.

  my_reflex.
  my_reflex.
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
  correct_forward. 2:{ (**r if-else branch *)
  unfold correct_body.
  intros.
  unfold Monad.returnM.
  unfold returnM.
  unfold Monad.returnM.
  intros.
  exists (Vint (Int.repr 0)), m, Events.E0.
  repeat split.

  repeat forward_star.
  intuition.
  constructor.
  reflexivity.
  }
  (**r if-then branch *)

  (** goal: correct_body p val (bindM (get_block_ptr c) *)
  eapply correct_statement_seq_body_pure.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  my_reflex.
  my_reflex.
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


  {
    unfold INV; intro H.
    correct_Forall.
    get_invariant _mr.
    exists (v::nil).
    split.
    unfold map_opt. unfold exec_expr. rewrite p0.
    reflexivity.
    intros. simpl.
    intuition. eauto.
  }
  intros.
  (** goal: correct_body _ _ (bindM (get_start_addr c) ... *)
  eapply correct_statement_seq_body_pure.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  my_reflex.
  my_reflex.
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
  eapply correct_statement_seq_body_pure.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  my_reflex.
  my_reflex.
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
  eapply correct_statement_seq_body_pure.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  my_reflex.
  my_reflex.
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
  eapply correct_statement_seq_body_pure.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  my_reflex.
  my_reflex.
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
  intuition; eauto. (**r we lost the evident that `correct_get_start_addr.match_res x0 v0 st3 m3` *)
  eauto. (**r we lost one very imporant information: the input/output constraints *)
  intros.
  (** goal:  correct_body _ _ (bindM (get_add x2 (memory_chunk_to_valu32 c1)) ... *)
  eapply correct_statement_seq_body_pure.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  my_reflex.
  my_reflex.
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

  (** goal: correct_body _ _ (if then else ... *)

  destruct (match x3 with
  | Vint n2 => negb (Int.ltu n2 Int.zero)
  | _ => false
  end && compu_lt_32 x4 x1) eqn: Hcond1.
  destruct (compu_le_32 x3 (memory_chunk_to_valu32_upbound c2) &&
  match val32_modu x3 (memory_chunk_to_valu32 c2) with
  | Vint n2 => Int.eq Int.zero n2
  | _ => false
  end) eqn: Hcond2.
  (**r we have three goals: 
    1. if-Hcond1-then-if-Hcond2-then
    2. if-Hcond1-then-if-Hcond2-else
    3. if-Hcond1-else
    *)
  3:{
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
    get_invariant _ptr.
    unfold correct_get_add.match_res, valu32_correct in c3.
    destruct c3 as (H0_eq & (vi0 & Hvi0_eq)).
    unfold correct_get_sub.match_res, valu32_correct in c4.
    destruct c4 as (H2_eq & (vi2 & Hvi2_eq)).
    unfold correct_get_block_size.match_res, valu32_correct in c5.
    destruct c5 as (H4_eq & (vi4 & Hvi4_eq)).
    unfold stateless, match_chunk, memory_chunk_to_valu32 in c6.
    unfold correct_get_block_ptr.match_res, val_ptr_correct in c7.
    destruct c7 as (H9_eq & (b & ofs & Hvi9_eq)).
    subst.

    exists (Vint Int.zero), m, Events.E0.
    repeat split.

    (**r we need the info given by Hcond1 *)
    assert (Hfalse: Int.ltu vi2 Int.zero = false). {
      unfold Int.ltu.
      rewrite Int.unsigned_zero. (**r Check zlt. *)
      destruct (zlt (Int.unsigned vi2) 0).
      assert (Hge: (Int.unsigned vi2) >= 0). { apply Int_unsigned_ge_zero. }
      lia.
      reflexivity.
    }
    rewrite Hfalse in Hcond1.
    unfold negb in Hcond1; simpl in Hcond1.


    forward_star. forward_star.

    simpl.
    fold Int.zero.
    rewrite Hfalse; simpl.
    reflexivity.

    forward_star.
    simpl.
    rewrite Hcond1.
    reflexivity.

    repeat forward_star.
    right.
    Transparent Archi.ptr64.
    unfold Vnullptr.
    reflexivity.

    constructor; reflexivity.
  }

  2:{ (**r 2. if-Hcond1-then-if-Hcond2-else *)
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
    get_invariant _ptr.
    unfold correct_get_add.match_res, valu32_correct in c3.
    destruct c3 as (H0_eq & (vi0 & Hvi0_eq)).
    unfold correct_get_sub.match_res, valu32_correct in c4.
    destruct c4 as (H2_eq & (vi2 & Hvi2_eq)).
    unfold correct_get_block_size.match_res, valu32_correct in c5.
    destruct c5 as (H4_eq & (vi4 & Hvi4_eq)).
    unfold stateless, match_chunk, memory_chunk_to_valu32 in c6.
    unfold correct_get_block_ptr.match_res, val_ptr_correct in c7.
    destruct c7 as (H9_eq & (b & ofs & Hvi9_eq)).
    subst.

    (**r we need the info given by Hcond1, Hcond2 *)
    assert (Hfalse: Int.ltu vi2 Int.zero = false). {
      unfold Int.ltu.
      rewrite Int.unsigned_zero. (**r Check zlt. *)
      destruct (zlt (Int.unsigned vi2) 0).
      assert (Hge: (Int.unsigned vi2) >= 0). { apply Int_unsigned_ge_zero. }
      lia.
      reflexivity.
    }
    rewrite Hfalse in Hcond1.
    unfold negb in Hcond1; simpl in Hcond1.
    (**r after we need the info about Hcond2, I do it here*)

    (**r we also need those info below *)
    assert (Hneq1: _lo_ofs <> _t'9). {
      unfold _lo_ofs, _t'9.
      intro Hneq; inversion Hneq.
    }
    assert (Hneq2: _chunk <> _t'9). {
      unfold _chunk, _t'9.
      intro Hneq; inversion Hneq.
    }
    
    assert (He: Int.modulus - 1 = 4294967295). {
      unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize; reflexivity.
    }
    assert (Hwell_chunk_unsigned: Int.unsigned (Int.repr (well_chunk_Z c2)) = well_chunk_Z c2). {
      destruct c2; simpl; try (fold Int.zero; apply Int.unsigned_zero); try rewrite Int.unsigned_repr; try reflexivity; try rewrite Int_max_unsigned_eq64; try lia.
    }

    assert (Hchunk_ne_zero: Int.eq (Int.repr (well_chunk_Z c2)) Int.zero = false). {
      unfold Int.zero.
      destruct c2; unfold Int.eq; simpl;
      repeat rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try apply zeq_false; try lia.
    }

    fold Int.zero Int.mone.
    exists (Vint Int.zero), m, Events.E0.
    repeat split.

    unfold val32_modu, memory_chunk_to_valu32, Val.modu in Hcond2.
    rewrite Hchunk_ne_zero in Hcond2.

    destruct (compu_le_32 (Vint vi2) (memory_chunk_to_valu32_upbound c2)) eqn: Heq1.
    (**r if lo_ofs <= 4294967295U - chunk then *)
    (**r Search (true && _). *)
    rewrite andb_true_l in Hcond2.
    unfold compu_le_32, memory_chunk_to_valu32_upbound in Heq1.
    rewrite Int_max_unsigned_eq64 in Heq1.

    forward_star. forward_star.
    simpl.
    rewrite Hfalse; reflexivity.
    forward_star.
    simpl.
    rewrite Hcond1; reflexivity.
    forward_star. forward_star.
    forward_star. forward_star.
    simpl.
    unfold Int.sub; rewrite Int.unsigned_mone.
    rewrite He.

    rewrite Hwell_chunk_unsigned.
    rewrite Heq1.
    reflexivity.

    forward_star.


    Transparent Archi.ptr64.
    simpl.
    unfold Cop.sem_mod, Cop.sem_binarith, Cop.sem_cast; simpl.

    rewrite Hchunk_ne_zero.
    reflexivity.

    reflexivity.
    simpl.
    rewrite Hcond2.
    reflexivity.

    forward_star. forward_star.
    forward_star. forward_star.
    forward_star. forward_star.
    simpl.

    rewrite Hfalse; unfold negb.
    reflexivity.

    forward_star.
    simpl.
    rewrite Hcond1;
    reflexivity.

    forward_star. forward_star.
    forward_star. forward_star.
    simpl.

    (**r if not lo_ofs <= 4294967295U - chunk then if 0U == lo_ofs % chunk then *)
    unfold compu_le_32, memory_chunk_to_valu32_upbound in Heq1.
    unfold Int.sub; rewrite Int.unsigned_mone.
    rewrite He.

    rewrite Hwell_chunk_unsigned.
    rewrite Int_max_unsigned_eq64 in Heq1.
    rewrite Heq1.
    reflexivity.

    forward_star. forward_star.
    forward_star. forward_star.
    forward_star.
    intuition.
    constructor; reflexivity.
  }

  (**r goal: correct_body p val (if rBPFMemType.perm_ge x2 c0 then returnM (Val.add x x3) else returnM valptr_null) fn (Ssequence (Sifthenelse ... *)
  destruct (rBPFMemType.perm_ge x2 c0) eqn: Hperm_ge.

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
    unfold returnM, Monad.returnM.
    intros.

    unfold INV0, INV in H.
    get_invariant _hi_ofs.
    get_invariant _lo_ofs.
    get_invariant _size.
    get_invariant _chunk.
    get_invariant _ptr.
    get_invariant _perm.
    get_invariant _mr_perm.

    unfold correct_get_add.match_res, valu32_correct in c3.
    destruct c3 as (H0_eq & (vi0 & Hvi0_eq)).
    unfold correct_get_sub.match_res, valu32_correct in c4.
    destruct c4 as (H2_eq & (vi2 & Hvi2_eq)).
    unfold correct_get_block_size.match_res, valu32_correct in c5.
    destruct c5 as (H4_eq & (vi4 & Hvi4_eq)).
    unfold stateless, match_chunk, memory_chunk_to_valu32 in c6.
    unfold correct_get_block_ptr.match_res, val_ptr_correct in c7.
    destruct c7 as (H9_eq & (b & ofs & Hvi9_eq)).
    unfold stateless, perm_correct in c8.
    unfold correct_get_block_perm.match_res, perm_correct in c9.
    subst.

    eexists; exists m, Events.E0.
    repeat split.
    Transparent Archi.ptr64.
    forward_star. forward_star.
    simpl.
    rewrite andb_true_iff in Hcond1.
    destruct Hcond1 as (Hcond1 & _).
    unfold Int.zero in Hcond1.
    rewrite negb_true_iff in Hcond1.
    rewrite Hcond1.
    reflexivity.

    forward_star. forward_star.
    simpl.
    rewrite andb_true_iff in Hcond1.
    destruct Hcond1 as (_ & Hcond1).
    unfold compu_lt_32 in Hcond1.
    rewrite Hcond1.
    reflexivity.

    forward_star. forward_star.
    forward_star. forward_star.
    simpl.
    rewrite andb_true_iff in Hcond2.
    destruct Hcond2 as (Hcond2 & _).
    unfold compu_le_32, memory_chunk_to_valu32_upbound in Hcond2.
    unfold Int.sub.
    assert (Hwell_chunk_unsigned: Int.unsigned (Int.repr (well_chunk_Z c2)) = well_chunk_Z c2). {
      destruct c2; simpl; try (fold Int.zero; apply Int.unsigned_zero); try rewrite Int.unsigned_repr; try reflexivity; try rewrite Int_max_unsigned_eq64; try lia.
    }
    rewrite Hwell_chunk_unsigned; clear Hwell_chunk_unsigned.
    fold Int.mone.
    rewrite Int.unsigned_mone.
    unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize.
    assert (Heq: two_power_nat 32 - 1 = 4294967295). { reflexivity. }
    rewrite Heq; clear Heq.
    rewrite Int_max_unsigned_eq64 in Hcond2.
    rewrite Hcond2.
    reflexivity.

    forward_star. forward_star.
    simpl.
    unfold Cop.sem_mod, Cop.sem_binarith; simpl.
    assert (Hchunk_ne_zero: Int.eq (Int.repr (well_chunk_Z c2)) Int.zero = false). {
      unfold Int.zero.
      destruct c2; unfold Int.eq; simpl;
      repeat rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try apply zeq_false; try lia.
    }
    rewrite Hchunk_ne_zero; clear Hchunk_ne_zero.
    reflexivity.

    reflexivity.
    unfold Cop.sem_cast; simpl.
    rewrite andb_true_iff in Hcond2.
    destruct Hcond2 as (_ & Hcond2).
    unfold val32_modu, memory_chunk_to_valu32, Val.modu,  Int.zero in Hcond2.
    destruct (Int.eq _ _) eqn: Hmodu; [inversion Hcond2 |].
    
    rewrite Hcond2.
    reflexivity.

    forward_star. forward_star.
    forward_star. forward_star.
    try post_process.

    simpl.
    unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
    unfold Cop.sem_cast; simpl.
    unfold rBPFMemType.perm_ge in Hperm_ge.
    destruct c0, x2; unfold Int.ltu; rewrite c8, c9; repeat rewrite Int_unsigned_repr_n; try reflexivity; try lia; simpl in Hperm_ge; inversion Hperm_ge.

    simpl.
    reflexivity.

    forward_star. forward_star.
    try post_process.
    reflexivity.
    reflexivity.
    simpl.
    fold Ptrofs.one.
    rewrite Ptrofs.mul_commut.
    rewrite Ptrofs.mul_one.
    forward_star.
    left.
    eexists; eexists; reflexivity.
    simpl.
    constructor.

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
    unfold returnM, Monad.returnM.
    intros.

    unfold INV0, INV in H.
    get_invariant _hi_ofs.
    get_invariant _lo_ofs.
    get_invariant _size.
    get_invariant _chunk.
    get_invariant _ptr.
    get_invariant _perm.
    get_invariant _mr_perm.

    unfold correct_get_add.match_res, valu32_correct in c3.
    destruct c3 as (H0_eq & (vi0 & Hvi0_eq)).
    unfold correct_get_sub.match_res, valu32_correct in c4.
    destruct c4 as (H2_eq & (vi2 & Hvi2_eq)).
    unfold correct_get_block_size.match_res, valu32_correct in c5.
    destruct c5 as (H4_eq & (vi4 & Hvi4_eq)).
    unfold stateless, match_chunk, memory_chunk_to_valu32 in c6.
    unfold correct_get_block_ptr.match_res, val_ptr_correct in c7.
    destruct c7 as (H9_eq & (b & ofs & Hvi9_eq)).
    unfold stateless, perm_correct in c8.
    unfold correct_get_block_perm.match_res, perm_correct in c9.
    subst.

    eexists; exists m, Events.E0.
    repeat split.
    forward_star. forward_star.
    simpl.

    rewrite andb_true_iff in Hcond1.
    destruct Hcond1 as (Hcond1 & _).
    unfold  Int.zero in Hcond1.
    rewrite negb_true_iff in Hcond1.
    rewrite Hcond1.
    reflexivity.

    forward_star.
    simpl.
    rewrite andb_true_iff in Hcond1.
    destruct Hcond1 as (_ & Hcond1).
    unfold compu_lt_32 in Hcond1.
    rewrite Hcond1.
    reflexivity.

    forward_star. forward_star.
    forward_star. forward_star.

    simpl.
    unfold compu_le_32, memory_chunk_to_valu32_upbound in Hcond2.
    unfold Int.sub.
    assert (Hwell_chunk_unsigned: Int.unsigned (Int.repr (well_chunk_Z c2)) = well_chunk_Z c2). {
      destruct c2; simpl; try (fold Int.zero; apply Int.unsigned_zero); try rewrite Int.unsigned_repr; try reflexivity; try rewrite Int_max_unsigned_eq64; try lia.
    }
    rewrite Hwell_chunk_unsigned; clear Hwell_chunk_unsigned.
    fold Int.mone.
    rewrite Int.unsigned_mone.
    unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize.
    assert (Heq: two_power_nat 32 - 1 = 4294967295). { reflexivity. }
    rewrite Heq; clear Heq.
    rewrite Int_max_unsigned_eq64 in Hcond2.
    rewrite andb_true_iff in Hcond2.
    destruct Hcond2 as (Hcond2 & _).
    rewrite Hcond2.
    reflexivity.

    forward_star.
    simpl.
    unfold Cop.sem_mod, Cop.sem_binarith; simpl.
    assert (Hchunk_ne_zero: Int.eq (Int.repr (well_chunk_Z c2)) Int.zero = false). {
      unfold Int.zero.
      destruct c2; unfold Int.eq; simpl;
      repeat rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try apply zeq_false; try lia.
    }
    rewrite Hchunk_ne_zero; clear Hchunk_ne_zero.
    reflexivity.

    reflexivity.
    unfold Cop.sem_cast; simpl.
    rewrite andb_true_iff in Hcond2.
    destruct Hcond2 as (_ & Hcond2).
    unfold val32_modu, memory_chunk_to_valu32, Val.modu,  Int.zero in Hcond2.
    destruct (Int.eq _ _) eqn: Hmodu; [inversion Hcond2 |].
    
    rewrite Hcond2.
    reflexivity.

    forward_star. forward_star.
    forward_star.
    post_process.
    post_process.
    simpl.
    unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
    unfold Cop.sem_cast; simpl.
    unfold rBPFMemType.perm_ge in Hperm_ge.
    destruct c0 eqn: Hc0_eq; destruct x2 eqn: Hx2_eq; inversion Hperm_ge; rewrite c8, c9; unfold Int.ltu; repeat rewrite Int_unsigned_repr_n; try reflexivity; try lia; simpl in Hperm_ge; inversion Hperm_ge.

    simpl.
    reflexivity.

    forward_star. forward_star.
    right.
    Transparent Archi.ptr64.
    unfold Vnullptr.
    reflexivity.
    constructor.

    reflexivity.
Qed.

End Check_mem_aux.

Close Scope Z_scope.

Existing Instance correct_function_check_mem_aux.
