From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues.
From bpf.src Require Import DxNat DxIntegers DxValues DxMonad DxInstructions.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.proof.correctproof Require Import correct_is_well_chunk_bool correct_get_sub correct_get_add correct_get_block_ptr correct_get_start_addr correct_get_block_size.

Open Scope Z_scope.

Section Check_mem_aux2.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(**r TODO: check_mem_aux2: memory_region -> perm -> addr -> chunk -> ptr *)

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition args  := [(memory_region:Type) ; (permission:Type); valu32_t; (AST.memory_chunk: Type)].
Definition res  := valptr8_t.

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
  DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
  DList.DCons
    (my_match_region bl_region)
    (DList.DCons
        (stateless perm_correct)
        (DList.DCons
           (stateless valu32_correct)
           (DList.DCons (stateless match_chunk)
                        (DList.DNil _)))).

Definition match_res (v1 :val) (v2:val) :=
  v1 = v2 /\ ((exists b ofs, v1 = Vptr b ofs) \/ v1 = val32_zero).


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
      eapply correct_statement_seq_body_pure;
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

Lemma correct_function_check_mem_aux2_correct : forall a, correct_function3 p args res f fn (nil) true match_arg (stateless match_res) a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f. unfold check_mem_aux2.
  simpl.
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
    unfold my_match_region in *.
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
  unfold Monad.returnM, val32_zero.
  unfold returnM.
  unfold Monad.returnM.
  intros.
  exists (Vint Int.zero), m, Events.E0.
  repeat split.

  forward_star.
  forward_star.
  unfold Int.zero.
  forward_star.
  reflexivity.
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
  unfold stateless, match_chunk, memory_chunk_to_valu32, well_chunk_Z in H2.
  intuition eauto.
  intros.
  (** goal: correct_body _ _ (if then else ... *)

  destruct (match x2 with
  | Vint n2 => negb (Int.ltu n2 int32_0)
  | _ => false
  end && compu_lt_32 x3 x1) eqn: Hcond1.
  destruct (compu_le_32 x2 (memory_chunk_to_valu32_upbound c2) &&
  match val32_modu x2 (memory_chunk_to_valu32 c2) with
  | Vint n2 => Int.eq int32_0 n2
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
    unfold returnM, val32_zero.
    intros.

    unfold INV0, INV in H.
    get_invariant_more _hi_ofs.
    get_invariant_more _lo_ofs.
    get_invariant_more _size.
    get_invariant_more _chunk.
    get_invariant_more _ptr.
    unfold correct_get_add.match_res, valu32_correct in H0.
    destruct H0 as (H0_eq & (vi0 & Hvi0_eq)).
    unfold correct_get_sub.match_res, valu32_correct in H2.
    destruct H2 as (H2_eq & (vi2 & Hvi2_eq)).
    unfold correct_get_block_size.match_res, valu32_correct in H4.
    destruct H4 as (H4_eq & (vi4 & Hvi4_eq)).
    unfold stateless, match_chunk, memory_chunk_to_valu32 in H6.
    unfold correct_get_block_ptr.match_res, val_ptr_correct in H8.
    destruct H8 as (H9_eq & (b & ofs & Hvi9_eq)).
    subst.

    exists (Vint Int.zero), m, Events.E0.
    repeat split.

    (**r we need the info given by Hcond1 *)
    unfold int32_0 in Hcond1.
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


    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star. (**r Search (_ && _ = false).*)

    simpl.
    fold Int.zero.
    rewrite Hfalse; simpl.
    reflexivity.

    rewrite Int_eq_one_zero; simpl.
    forward_star.
    repeat forward_star.
    simpl.
    rewrite Hcond1.
    reflexivity.

    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gss.
    reflexivity.
    rewrite Int.eq_true.
    reflexivity.

    forward_star.
    repeat forward_star.
    rewrite Int.eq_true; unfold negb.

    forward_star.
    forward_star.
    reflexivity.
    intuition.

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
    unfold returnM, val32_zero.
    intros.

    unfold INV0, INV in H.
    get_invariant_more _hi_ofs.
    get_invariant_more _lo_ofs.
    get_invariant_more _size.
    get_invariant_more _chunk.
    get_invariant_more _ptr.
    unfold correct_get_add.match_res, valu32_correct in H0.
    destruct H0 as (H0_eq & (vi0 & Hvi0_eq)).
    unfold correct_get_sub.match_res, valu32_correct in H2.
    destruct H2 as (H2_eq & (vi2 & Hvi2_eq)).
    unfold correct_get_block_size.match_res, valu32_correct in H4.
    destruct H4 as (H4_eq & (vi4 & Hvi4_eq)).
    unfold stateless, match_chunk, memory_chunk_to_valu32 in H6.
    unfold correct_get_block_ptr.match_res, val_ptr_correct in H8.
    destruct H8 as (H9_eq & (b & ofs & Hvi9_eq)).
    subst.

    (**r we need the info given by Hcond1, Hcond2 *)
    unfold int32_0 in Hcond1, Hcond1.
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

    unfold val32_modu, memory_chunk_to_valu32, Val.modu, int32_0 in Hcond2.
    rewrite Hchunk_ne_zero in Hcond2.

    destruct (compu_le_32 (Vint vi2) (memory_chunk_to_valu32_upbound c2)) eqn: Heq1.
    (**r if lo_ofs <= 4294967295U - chunk then *)
    (**r Search (true && _). *)
    rewrite andb_true_l in Hcond2.
    unfold compu_le_32, memory_chunk_to_valu32_upbound in Heq1.
    rewrite Int_max_unsigned_eq64 in Heq1.

    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    simpl.
    rewrite Hfalse; reflexivity.
    rewrite Int_eq_one_zero; unfold negb.
    forward_star.
    repeat forward_star.
    simpl.
    rewrite Hcond1; reflexivity.
    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gss.
    rewrite Int_eq_one_zero; reflexivity.
    reflexivity.
    forward_star.
    repeat forward_star.
    rewrite Int_eq_one_zero; unfold negb.
    forward_star.
    forward_star.
    forward_star.
    rewrite Maps.PTree.gso.
    rewrite p1; reflexivity.
    assumption.
    rewrite Maps.PTree.gso.
    rewrite p3; reflexivity.
    assumption.
    reflexivity.
    reflexivity.
    simpl.
    unfold Int.sub; rewrite Int.unsigned_mone.
    rewrite He.

    rewrite Hwell_chunk_unsigned.
    rewrite Heq1.
    reflexivity.

    forward_star.
    repeat forward_star.
    rewrite Int_eq_one_zero; unfold negb.
    repeat forward_star.
    rewrite Maps.PTree.gso.
    rewrite p1; reflexivity.
    assumption.
    rewrite Maps.PTree.gso.
    rewrite p3; reflexivity.
    assumption.
    simpl.


    Transparent Archi.ptr64.
    unfold Cop.sem_mod, Cop.sem_binarith, Cop.sem_cast; simpl.

    rewrite Hchunk_ne_zero.
    reflexivity.

    reflexivity.
    simpl.
    rewrite Hcond2.
    reflexivity.

    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gss.
    reflexivity.
    reflexivity.
    repeat rewrite Int.eq_true; unfold negb.
    forward_star.
    repeat forward_star.
    forward_star.
    reflexivity.

    (**r if not lo_ofs <= 4294967295U - chunk then if 0U == lo_ofs % chunk then *)
    unfold compu_le_32, memory_chunk_to_valu32_upbound in Heq1.
    (**r Search (_ && _ = false).*)
    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    simpl.

    rewrite Hfalse; unfold negb.
    reflexivity.

    forward_star.
    repeat forward_star.
    rewrite Int_eq_one_zero; unfold negb.
    forward_star.
    repeat forward_star.
    simpl.
    rewrite Hcond1;
    reflexivity.

    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gss.
    reflexivity.
    reflexivity.
    repeat rewrite Int_eq_one_zero; unfold negb.

    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gso.
    rewrite p1; reflexivity.
    assumption.
    rewrite Maps.PTree.gso.
    rewrite p3; reflexivity.
    assumption.
    reflexivity.
    reflexivity.
    simpl.

    fold Int.mone.
    unfold Int.sub; rewrite Int.unsigned_mone.
    rewrite He.

    rewrite Hwell_chunk_unsigned.
    rewrite Int_max_unsigned_eq64 in Heq1.
    rewrite Heq1.
    reflexivity.
    rewrite Int.eq_true; unfold negb.

    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    forward_star.
    repeat forward_star.
    rewrite Maps.PTree.gss.
    reflexivity.
    reflexivity.
    rewrite Int.eq_true; unfold negb.
    forward_star.
    repeat forward_star.
    forward_star.
    reflexivity.
    intuition.
    constructor; reflexivity.
  }
  (**r goal: correct_body p val (bindM (get_block_perm c) ... *)
  TODO.
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
  destruct (returnM (Val.add x x2) st5) eqn: Hreturn; [idtac | constructor].
  unfold returnM in Hreturn.
  destruct p0.
  intros.

  (**r we need the value of those vairable in the memory, they will be used later *)
  unfold INV0, INV in H.
  get_invariant_more _hi_ofs.
  get_invariant_more _lo_ofs.
  get_invariant_more _size.
  get_invariant_more _chunk.
  get_invariant_more _ptr.
  unfold correct_get_add.match_res, valu32_correct in H0.
  destruct H0 as (H0_eq & (vi0 & Hvi0_eq)).
  unfold correct_get_sub.match_res, valu32_correct in H2.
  destruct H2 as (H2_eq & (vi2 & Hvi2_eq)).
  unfold correct_get_block_size.match_res, valu32_correct in H4.
  destruct H4 as (H4_eq & (vi4 & Hvi4_eq)).
  unfold stateless, match_chunk, memory_chunk_to_valu32 in H6.
  unfold correct_get_block_ptr.match_res, val_ptr_correct in H8.
  destruct H8 as (H9_eq & (b & ofs & Hvi9_eq)).
  subst.

  exists (Val.add (Vptr b ofs) (Vint vi2)), m, Events.E0.
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
    assert (Hvi3_ge: ((Int.unsigned vi2) >= 0)%Z). {
      assert (Hhi_range: (0 <= Int.unsigned vi2 <= Int.max_unsigned)%Z).
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
    unfold Cop.sem_binary_operation, Cop.sem_add, Cop.classify_add; simpl.
    reflexivity.
    reflexivity.

    unfold Ptrofs.mul, Ptrofs.of_intu.
    assert (Hofs_one: Ptrofs.unsigned (Ptrofs.repr 1) = 1). {
      apply Ptrofs.unsigned_repr.
      rewrite Ptrofs_max_unsigned_eq32.
      lia.
    }
    rewrite Hofs_one.
    rewrite Z.mul_1_l.
    rewrite Ptrofs.repr_unsigned.
    constructor.
    reflexivity.
  + inversion Hreturn.
    reflexivity.
  + inversion Hreturn.
    left; exists b, (Ptrofs.add ofs (Ptrofs.of_int vi2)).
    reflexivity.
  + constructor.
  + inversion Hreturn.
    reflexivity.
Qed.

End Check_mem_aux2.

Close Scope Z_scope.

Existing Instance correct_function_check_mem_aux2_correct.
