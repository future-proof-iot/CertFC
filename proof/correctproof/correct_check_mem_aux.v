From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.src Require Import DxIntegers DxValues DxAST DxMemRegion DxState DxMonad DxInstructions.
From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.proof.correctproof Require Import correct_is_well_chunk_bool correct_get_sub correct_get_add correct_get_block_ptr correct_get_start_addr correct_get_block_size.

Open Scope Z_scope.

Section Check_mem_aux2.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition args  := [(memory_region:Type) ; valu32_t; (AST.memory_chunk: Type)].
Definition res  := valu32_t.

(* [f] is a Coq Monadic function with the right type *)
Definition f := check_mem_aux2.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_check_mem_aux2.

Definition is_vlong (v: val) :=
  match v with
  | Vlong _ => True
  | _       => False
  end.

Variable bl_region : block.

Definition match_arg  :
  DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
  DList.DCons
    (my_match_region bl_region)
    (DList.DCons
       (stateless valu32_correct)
       (DList.DCons (stateless match_chunk)
                    (DList.DNil _))).

Lemma Int_eq_one_zero :
  Int.eq Int.one Int.zero = false.
Proof.
  reflexivity.
Qed.

Record match_res (v1 :val) (v2:val) (st:stateM) (m: Memory.Mem.mem)  :=
  {
    res_eq : v1 = v2
  }.


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

Ltac correct_forward :=
  match goal with
  | |- @correct_body _ _ (bindM ?F1 ?F2)  _
                     (Ssequence
                        (Ssequence
                           (Scall _ _ _)
                           (Sset ?V ?T))
                        ?R)
                     _ _ _ _ _ _  =>
      eapply correct_statement_seq_body;
      [ change_app_for_statement ;
        let b := match T with
                 | Ecast _ _ => constr:(true)
                 | _         => constr:(false)
                 end in
        eapply correct_statement_call with (has_cast := b)
      |]
  | |- @correct_body _ _ (match  ?x with true => _ | false => _ end) _
                     (Sifthenelse _ _ _)
                     _ _ _ _ _ _  =>
      eapply correct_statement_if_body; [prove_in_inv | destruct x ]
  end.

Lemma correct_function_check_mem_aux_correct : forall a, correct_function3 p args res f fn (nil) true match_arg match_res a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f. unfold check_mem_aux2.
  simpl.
  (** goal: correct_body _ _ (bindM (is_well_chunk_bool ... *)
  correct_forward.

  reflexivity.
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
    eapply same_my_memory_match_region;eauto.
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
  correct_forward.
  (** goal: correct_body p val (bindM (get_block_ptr c) *)
  eapply correct_statement_seq_body.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  reflexivity.
  reflexivity.
  reflexivity.
  typeclasses eauto.
  { unfold INV.
    unfold var_inv_preserve.
    intros.
    unfold match_temp_env in *.
    rewrite Forall_fold_right in *.
    simpl in *.
    intuition. clear - H1 H.
    unfold match_elt in *;
      unfold fst in *.
    destruct (Maps.PTree.get _mr le0);auto.
    simpl in *.
    destruct H1 ; split; auto.
    eapply same_my_memory_match_region;eauto.
  }
  reflexivity.
  reflexivity.
  reflexivity.
  prove_in_inv.
  prove_in_inv.
  reflexivity.
  reflexivity.
  intros.
  {
    intros.
    change (match_temp_env (((_well_chunk, Clightdefs.tbool, stateless match_bool true) :: INV)) le0 st0 m0) in H.
    unfold INV in H.
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
  eapply correct_statement_seq_body.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  reflexivity.
  reflexivity.
  reflexivity.
  typeclasses eauto.
  { unfold INV.
    unfold var_inv_preserve.
    intros.
    unfold match_temp_env in *.
    rewrite Forall_fold_right in *.
    simpl in *.
    intuition. clear - H3 H.
    unfold match_elt in *;
      unfold fst in *.
    destruct (Maps.PTree.get _mr le1);auto.
    simpl in *.
    destruct H3 ; split; auto.
    eapply same_my_memory_match_region;eauto.
  }
  reflexivity.
  reflexivity.
  reflexivity.
  prove_in_inv.
  prove_in_inv.
  reflexivity.
  reflexivity.
  intros.
  change (match_temp_env ((_ptr, Clightdefs.tuint, correct_get_block_ptr.match_res x)
                            :: (_well_chunk, Clightdefs.tbool, stateless match_bool true) :: INV) le1 st1 m1) in H.
  unfold INV in H.
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
  eapply correct_statement_seq_body.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  reflexivity.
  reflexivity.
  reflexivity.
  typeclasses eauto.
  { unfold INV.
    unfold var_inv_preserve.
    intros.
    unfold match_temp_env in *.
    rewrite Forall_fold_right in *.
    simpl in *.
    intuition. clear - H4 H.
    unfold match_elt in *;
      unfold fst in *.
    destruct (Maps.PTree.get _mr le2); auto.
    simpl in *.
    destruct H4; split; auto.
    eapply same_my_memory_match_region;eauto.
  }
  reflexivity.
  reflexivity.
  reflexivity.
  prove_in_inv.
  prove_in_inv.
  reflexivity.
  reflexivity.
  intros.
  change (match_temp_env ((_start, Clightdefs.tuint, correct_get_start_addr.match_res x0)
       :: (_ptr, Clightdefs.tuint, correct_get_block_ptr.match_res x)
       :: (_well_chunk, Clightdefs.tbool, stateless match_bool true) :: INV) le2 st2 m2) in H.
  unfold INV in H.
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
  eapply correct_statement_seq_body.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  reflexivity.
  reflexivity.
  reflexivity.
  typeclasses eauto.
  { unfold INV.
    unfold var_inv_preserve.
    intros.
    unfold match_temp_env in *.
    rewrite Forall_fold_right in *.
    simpl in *.
    intuition. clear - H5 H.
    unfold match_elt in *;
      unfold fst in *.
    destruct (Maps.PTree.get _mr le3); auto.
    simpl in *.
    destruct H5; split; auto.
    eapply same_my_memory_match_region;eauto.
  }
  reflexivity.
  reflexivity.
  reflexivity.
  prove_in_inv.
  prove_in_inv.
  reflexivity.
  reflexivity.
  intros.
  change (match_temp_env ((_size, Clightdefs.tuint, correct_get_block_size.match_res x1)
       :: (_start, Clightdefs.tuint, correct_get_start_addr.match_res x0)
          :: (_ptr, Clightdefs.tuint, correct_get_block_ptr.match_res x)
             :: (_well_chunk, Clightdefs.tbool, stateless match_bool true) :: INV) le3 st3 m3) in H.
  unfold INV in H.
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
  eapply correct_statement_seq_body.
  change_app_for_statement.
  eapply correct_statement_call with (has_cast := false).
  reflexivity.
  reflexivity.
  reflexivity.
  typeclasses eauto.
  { unfold INV.
    unfold var_inv_preserve.
    intros.
    unfold match_temp_env in *.
    rewrite Forall_fold_right in *.
    simpl in *.
    intuition. clear - H6 H.
    unfold match_elt in *;
      unfold fst in *.
    destruct (Maps.PTree.get _mr le4); auto.
    simpl in *.
    destruct H6; split; auto.
    eapply same_my_memory_match_region;eauto.
  }
  reflexivity.
  reflexivity.
  reflexivity.
  prove_in_inv.
  prove_in_inv.
  reflexivity.
  reflexivity.
  intros.
  change (match_temp_env ((_lo_ofs, Clightdefs.tuint, correct_get_sub.match_res x2)
     :: (_size, Clightdefs.tuint, correct_get_block_size.match_res x1)
        :: (_start, Clightdefs.tuint, correct_get_start_addr.match_res x0)
           :: (_ptr, Clightdefs.tuint, correct_get_block_ptr.match_res x)
              :: (_well_chunk, Clightdefs.tbool, stateless match_bool true)
                 :: INV) le4 st4 m4) in H.
  unfold INV in H.
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
  unfold stateless, match_chunk, memory_chunk_to_valu32, well_chunk_Z in H2.
  intuition eauto.
  intros.
  (** goal: correct_body _ _ (if then else ... *)

  destruct (match x2 with
  | Vint n2 => negb (Int.ltu n2 int32_0)
  | _ => false
  end && compu_lt_32 x3 x1) eqn: Hcond1.
  destruct (compu_le_32 x2 (memory_chunk_to_valu32_upbound c1) &&
  match val32_modu x2 (memory_chunk_to_valu32 c1) with
  | Vint n2 => Int.eq int32_0 n2
  | _ => false
  end) eqn: Hcond2.
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
  intro.
  destruct (returnM (Val.add x x2) st5); [idtac | constructor].
  destruct p0.
  intros.

  (**r we need the value of those vairable in the memory, they will be used later *)
  unfold INV0,INV in H.
  get_invariant_more _hi_ofs.
  get_invariant_more _lo_ofs.
  get_invariant_more _size.
  get_invariant_more _chunk.
  get_invariant_more _ptr.
  unfold correct_get_add.match_res, valu32_correct in H1.
  destruct H1 as (H1_eq & (vi1 & Hvi1_eq)).
  unfold correct_get_sub.match_res, valu32_correct in H3.
  destruct H3 as (H3_eq & (vi3 & Hvi3_eq)).
  unfold correct_get_block_size.match_res, valu32_correct in H5.
  destruct H5 as (H5_eq & (vi5 & Hvi5_eq)).
  unfold stateless, match_chunk, memory_chunk_to_valu32 in H7.
  unfold correct_get_block_ptr.match_res, valu32_correct in H9.
  destruct H9 as (H10_eq & (vi10 & Hvi10_eq)).
  subst.

  eexists. exists m, Events.E0.
  repeat split.
  + 
    Transparent Archi.ptr64.
    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    unfold Cop.bool_val, Val.of_bool, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
    unfold Int.ltu.
    fold Int.zero.
    rewrite Int.unsigned_zero.
    assert (Hvi3_ge: ((Int.unsigned vi3) >= 0)%Z). {
      assert (Hhi_range: (0 <= Int.unsigned vi3 <= Int.max_unsigned)%Z).
      apply Int.unsigned_range_2.
      lia.
    }
    rewrite zlt_false; simpl.
    rewrite Int_eq_one_zero; reflexivity.
    assumption.

    (** Smallstep.star _ _ (State _ (if negb false ... *)
    simpl.
    forward_star.
    forward_star.
    unfold Cop.sem_cast, Val.of_bool; simpl.
    apply andb_prop in Hcond1.
    destruct Hcond1 as (Hcond1_1 & Hcond1_2).
    unfold compu_lt_32 in Hcond1_2.
    rewrite Hcond1_2; simpl.
    rewrite Int_eq_one_zero; reflexivity.
    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gss; reflexivity.
    reflexivity.
    (** Smallstep.star _ _(State _ (if negb (Int.eq Int.one Int.zero) then ... *)
    forward_star.
    rewrite Int_eq_one_zero.
    unfold negb.
    repeat forward_star.

    (**r after we need the info about Hcond2, I do it here*)
    apply andb_prop in Hcond2.
    destruct Hcond2 as (Hcond2_1 & Hcond2_2).
    unfold compu_le_32, memory_chunk_to_valu32_upbound in Hcond2_1.
    rewrite Int_max_unsigned_eq64 in Hcond2_1.
    unfold val32_modu, Val.modu, memory_chunk_to_valu32 in Hcond2_2.
    
    destruct (Int.eq (Int.repr (well_chunk_Z c1)) Int.zero) eqn: Heq_zero; try discriminate.

    (**r we also need those info below *)
    assert (Hneq1: _lo_ofs <> _t'8). {
      unfold _lo_ofs, _t'8.
      intro Hneq; inversion Hneq.
    }
    assert (Hneq2: _chunk <> _t'8). {
      unfold _chunk, _t'8.
      intro Hneq; inversion Hneq.
    }

    forward_star.
    forward_star.
    (**r the 1st place I need _lo_ofs & _chunk *)
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=le5) in Hneq1.
    rewrite Hneq1.
    rewrite p1; reflexivity.
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=le5) in Hneq2.
    rewrite Hneq2.
    rewrite p3; reflexivity.
    reflexivity.
    reflexivity.
    unfold Cop.bool_val, Val.of_bool; simpl.

    (**the first place I need Hcond2 *)
    fold Int.mone.
    unfold Int.sub; rewrite Int.unsigned_mone.
    assert (He: Int.modulus - 1 = 4294967295). {
      unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize; reflexivity.
    }
    rewrite He.

    assert (Hwell_chunk_unsigned: Int.unsigned (Int.repr (well_chunk_Z c1)) = well_chunk_Z c1). {
      destruct c1; simpl; try (fold Int.zero; apply Int.unsigned_zero); try rewrite Int.unsigned_repr; try reflexivity; try rewrite Int_max_unsigned_eq64; try lia.
    }
    rewrite Hwell_chunk_unsigned.
    rewrite Hcond2_1; simpl.
    rewrite Int_eq_one_zero; unfold negb; reflexivity.
    Search (if true then _ else _).
    match goal with
    | |- context[if true then ?X else ?Y] =>
        change (if true then X else Y) with X
    end.

    forward_star.
    forward_star.
    (**r the 2nd place I need _lo_ofs & _chunk *)
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=le5) in Hneq1.
    rewrite Hneq1.
    rewrite p1; reflexivity.
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=le5) in Hneq2.
    rewrite Hneq2.
    rewrite p3; reflexivity.

    unfold Cop.sem_binary_operation; simpl.
    unfold Cop.sem_mod, Cop.sem_binarith; simpl.
    (**r here we need to prove `modu`, i.e. (well_chunk_Z c1) <> 0, we should see the Hypothesis `Hcond2` *)
    rewrite Heq_zero;
    reflexivity.
    reflexivity.

    unfold Cop.bool_val, Val.of_bool; simpl.
    unfold int32_0, Int.zero in Hcond2_2.
    rewrite Hcond2_2.
    reflexivity.

    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gss.
    rewrite Int_eq_one_zero.
    reflexivity.
    reflexivity.

    rewrite Int_eq_one_zero; unfold negb.
    forward_star.
    repeat forward_star.
    assert (Hneq3: _ptr <> _t'7). {
      unfold _ptr, _t'7.
      intro Hneq; inversion Hneq.
    }
    assert (Hneq4: _ptr <> _t'8). {
      unfold _ptr, _t'8.
      intro Hneq; inversion Hneq.
    }
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=(Maps.PTree.set _t'8 (Vint Int.one) le5)) in Hneq3; rewrite Hneq3.
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=le5) in Hneq4; rewrite Hneq4.
    rewrite p4; reflexivity.
    assert (Hneq3: _lo_ofs <> _t'7). {
      unfold _lo_ofs, _t'7.
      intro Hneq; inversion Hneq.
    }
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=(Maps.PTree.set _t'8 (Vint Int.one) le5)) in Hneq3; rewrite Hneq3.
    apply Maps.PTree.gso with (x:=Vint Int.one) (m:=le5) in Hneq1; rewrite Hneq1.
    rewrite p1; reflexivity.
    reflexivity.
    reflexivity.

    (**r we need to show : Vint (Int.add vi10 vi3)) = v && m = m5 *)
    simpl.
    Check Maps.PTree.gso.
    
    simpl.


    
  admit.
 
  (* TODO .... *)


  repeat intro.
  repeat eexists.
  eapply Smallstep.star_step;eauto.
  econstructor ; eauto.
  econstructor ; eauto.
  simpl. reflexivity.
  reflexivity.
  eapply Smallstep.star_refl.
  constructor.
Admitted.



End Check_mem_aux.

Close Scope Z_scope.
