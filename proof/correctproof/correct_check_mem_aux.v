From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.src Require Import DxIntegers DxValues DxAST DxMemRegion DxState DxMonad DxInstructions.
From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.proof.correctproof Require Import correct_is_well_chunk_bool correct_get_sub correct_get_add correct_get_block_ptr correct_get_start_addr correct_get_block_size.

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
  intros. unfold args in a.
  car_cdr.
  correct_function_from_body.
  correct_body.
  unfold f. unfold check_mem_aux2.
  simpl.
  (** goal: correct_body _ _ (bindM (is_well_chunk_bool ... *)
  correct_forward.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - typeclasses eauto.
  -  {  unfold INV.
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
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - prove_in_inv.
  - prove_in_inv.
  - reflexivity.
  - reflexivity.
  - intros.
    change (match_temp_env INV le st m) in H.
    unfold INV in H.
    get_invariant _chunk.
    exists (v::nil).
    split.
    unfold map_opt. unfold exec_expr. rewrite p0.
    reflexivity.
    intros. simpl.
    tauto.
  -
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
    end && compu_lt_32 x3 x1).
    destruct (compu_le_32 x2 (memory_chunk_to_valu32_upbound c1) &&
    match val32_modu x2 (memory_chunk_to_valu32 c1) with
    | Vint n2 => Int.eq int32_0 n2
    | _ => false
    end).
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

    eexists. exists m, Events.E0.
    forward_star.
    repeat forward_star.
    eapply correct_statement_seq_body.
    change_app_for_statement.
    eapply correct_statement_call with (has_cast := false).
    apply st5.

    TODO. 
    rewrite Hv0_eq in *.
    simpl.
    eexists.
    split.
    reflexivity.
    simpl.
    (**  exists lval : list val, _ [Etempvar _lo_ofs _; Ecast (Etempvar _chunk1 _) _] = Some lval *)
    exists ([v; (Vlong (v0)]).
    split.
   
    rewrite p0, p1.
    simpl.
    unfold Cop.sem_cast; simpl. (**r `Maps.PTree.get _chunk1 le4 = Some v0` where v0 should be Vint *)
    unfold Int.one. (** Vlong vs vint: we could generate u64 chunk by dx *)
    destruct c1; rewrite Int.unsigned_repr. reflexivity.
    reflexivity.
    simpl;intros.
    intuition eauto.

    
  admit.
  intros.
  (** goal: correct_body _ _ (bindM (get_subl ... *)
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
    destruct (Maps.PTree.get _mr3 le3); auto.
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
  admit.
  intros.
  (** goal: correct_body _ _ (bindM (get_addl ... *)
  unfold memory_chunk_to_val64.
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
    destruct (Maps.PTree.get _mr3 le4); auto.
    simpl in *.
    destruct H6; split; auto.
    eapply same_my_memory_match_region;eauto.
  }
  (** here is a casting from u32 -> u64 *)
  reflexivity.
  reflexivity.
  reflexivity.
  prove_in_inv.
  prove_in_inv.
  reflexivity.
  reflexivity.
  intros.
  change (match_temp_env ((_lo_ofs, Clightdefs.tulong, correct_get_subl.match_res x2)
         :: (_size, Clightdefs.tulong,
            correct_getMemRegion_block_size.match_res x1)
            :: (_start, Clightdefs.tulong,
               correct_getMemRegion_start_addr.match_res x0)
               :: (_ptr, Clightdefs.tulong,
                  correct_getMemRegion_block_ptr.match_res x)
                  :: (_well_chunk, Clightdefs.tbool, stateless match_bool true)
                     :: INV) le4 st4 m4) in H.
  get_invariant _lo_ofs.
  unfold INV in H.
  get_invariant _chunk1.
  destruct c3.
  assert (exists v, Cop.sem_cast v0 Clightdefs.tuint Clightdefs.tulong m4 = Some v).
  {
    inv H1.
    unfold Cop.sem_cast.
    simpl.
    eexists ; reflexivity.
    unfold stateless,match_chunk in H0.
    discriminate.
  }
  destruct H2 as (v1 & C).
  exists (v::v1::nil).
  split.
  unfold map_opt,exec_expr.
  rewrite p0. rewrite p1.
  simpl. rewrite C. reflexivity.
  simpl.
  (* TODO .... *)


  {
    intros. (** l' is map_opt _ l' *)
    apply match_temp_env_ex with (l':= [(_addr0, Clightdefs.tulong); (_start, Clightdefs.tulong)]) in H.
    destruct H.
    exists x2. split; auto.
    apply length_map_opt in H.
    rewrite <- H. reflexivity.
    unfold INV, incl; simpl.
    intuition subst;discriminate.
  }
  intros.



  [
          reflexivity
          | reflexivity
          | reflexivity
          | typeclasses eauto
          | idtac
          | reflexivity
          | reflexivity
          | reflexivity
          | reflexivity
          | prove_incl
          | prove_in_inv
          | prove_in_inv
          | idtac
         ].
  
      [ change_app_for_statement ;
        let b := match T with
                 | Ecast _ _ => constr:(true)
                 | _         => constr:(false)
                 end in
        eapply correct_statement_call with (has_cast := b);
        [
          reflexivity
          | reflexivity
          | reflexivity
          | typeclasses eauto
          | idtac
          | reflexivity
          | reflexivity
          | reflexivity
          | reflexivity
          | prove_incl
          | prove_in_inv
          | prove_in_inv
          | idtac
         ]
      |]
  correct_forward.
  unfold getMemRegion_block_ptr. Print correct_getMemRegion_block_ptr.correct_function3_getMemRegion_block_ptr.
  unfold bindM.
  unfold runM, returnM.
  
  match goal with
    | |- @correct_body _ _ 
  unfold getMemRegion_start_addr.
  admit.
  (* TODO *)
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
