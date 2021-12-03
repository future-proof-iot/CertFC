From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From dx.tests Require Import DxIntegers DxValues DxAST DxMemRegion DxState DxMonad DxInstructions.
From compcert Require Import Coqlib Values Clight Memory Integers.
Require Import StateBlock MatchState.
Require Import Clightlogic interpreter.


Require Import correct_is_well_chunk_bool.
Require Import clight_exec CommonLemma.

Section Check_mem_aux.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition args  := [(memory_region:Type) ; val64_t; (AST.memory_chunk: Type)].
Definition res  := val64_t.

(* [f] is a Coq Monadic function with the right type *)
Definition f := check_mem_aux.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_check_mem_aux.

Definition is_vlong (v: val) :=
  match v with
  | Vlong _ => True
  | _       => False
  end.

Definition val64_correct (v v':val) :=
  v = v'.

Definition match_region (mr: memory_region) (v: val64_t) (st: stateM) (m:Memory.Mem.mem) :=
  exists bl_region o, v = Vptr bl_region (Ptrofs.mul size_of_region  o) /\
              match_region mr bl_region o m.


Definition match_arg  :
  DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
  DList.DCons
    match_region
    (DList.DCons
       (stateless val64_correct)
       (DList.DCons (stateless match_chunk)
                    (DList.DNil _))).


Ltac nameK K :=
  match goal with
  | |-context[
          (Callstate _ _ ?k _)] =>

      set (K:= k)
  end.

(*Lemma bool_correct_Vint : forall r m v,
    bool_correct r m v <-> v = Vint (if r then Int.one else Int.zero).
Proof.
  unfold bool_correct. intros.
  destruct r;reflexivity.
Qed.
*)
Lemma Int_eq_one_zero :
  Int.eq Int.one Int.zero = false.
Proof.
  reflexivity.
Qed.




Record match_res (v1 :val) (v2:val) (st:stateM) (m: Memory.Mem.mem)  :=
  {
    res_eq : v1 = v2
  }.

Lemma same_memory_match_region :
  forall st st' m m' mr v
         (UMOD : unmodifies_effect [] m m'),
    match_region mr v st m ->
    match_region mr v st' m'.
Proof.
  intros.
  unfold match_region in *.
  destruct H as (bl_region & o & E & MR).
  exists bl_region, o.
  split; auto.
  unfold MatchState.match_region in *.
  unfold unmodifies_effect in UMOD.
  unfold Mem.loadv.
  repeat rewrite <- UMOD by (simpl ; tauto).
  intuition.
Qed.

Lemma match_temp_env_ex : forall l' l le st m ,
    incl l' (List.map fst l) ->
    match_temp_env l le st m ->
  exists lval : list val,
    map_opt (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)
      l' = Some lval.
Proof.
  induction l'.
  - simpl.
    intros. exists nil.
    reflexivity.
  - intros.
    simpl.
    assert (In a (List.map fst l)).
    apply H. simpl. tauto.
    apply List.incl_cons_inv in H.
    destruct H as (IN & INCL).
    assert (H0':= H0).
    eapply IHl' in H0'; eauto.
    destruct H0'.
    unfold match_temp_env in H0.
    rewrite Forall_forall in H0.
    rewrite in_map_iff in IN.
    destruct IN as (v' & FST & IN).
    subst. apply H0 in IN.
    unfold match_elt in IN.
    unfold AST.ident in *.
    destruct (Maps.PTree.get (fst (fst v')) le); try tauto.
    rewrite H.
    eexists. reflexivity.
Qed.





Lemma correct_function_check_mem_aux_correct : correct_function3 p args res f fn (nil) true match_arg match_res.
Proof.
  correct_function_from_body.
  intros.
  unfold args in a.
  car_cdr.
  unfold list_rel_arg.
  unfold Clightlogic.app.
  set (INV := (combine (fn_params fn)
       (list_rel (all_args args true) match_arg
          (all_args_list args true
             (DList.DCons c
                (DList.DCons c0
                   (DList.DCons c1 (DList.DNil (fun x : Type => x))))))))).
  simpl in INV.
  unfold f. unfold check_mem_aux.
  unfold fn at 2.
  unfold f_check_mem_aux.
  unfold fn_body.
  apply correct_statement_seq_body with
      (match_res1 := stateless match_bool)
      (vret := _well_chunk) (ti:= Clightdefs.tbool).
  change (is_well_chunk_bool c1) with (app (is_well_chunk_bool : arrow_type ((AST.memory_chunk:Type)::nil) (M bool)) (DList.DCons c1 (DList.DNil _))).
    {  eapply correct_statement_call with (has_cast := true).
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * apply correct_function_is_well_chunk_bool2.
    * unfold INV.
      unfold var_inv_preserve.
      intros.
      unfold match_temp_env in *.
      rewrite Forall_fold_right in *.
      simpl in *.
      intuition. clear - H2 H.
      unfold match_elt in *;
      unfold fst in *.
      destruct (Maps.PTree.get _mr3 le);auto.
      simpl in *.
      destruct H2 ; split; auto.
      eapply same_memory_match_region;eauto.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * simpl. unfold INV.
      unfold incl.
      simpl. intuition congruence.
    * simpl. intuition subst; discriminate.
    * simpl. intuition subst; discriminate.
    * intros.
      apply match_temp_env_ex with (l':= [(_chunk1, Clightdefs.tuint)]) in H.
      destruct H.
      exists x. split; auto.
      apply length_map_opt in H.
      rewrite <- H. reflexivity.
      unfold INV, incl; simpl.
      intuition subst;discriminate.
    }
    intros.
    eapply correct_statement_if_body.
    {
      simpl. tauto.
    }
    destruct x.
    apply correct_statement_seq_body with
      (match_res1 := stateless val64_correct)
      (vret := _ptr) (ti:= Clightdefs.tulong).
    change (getMemRegion_block_ptr c) with
      (app (getMemRegion_block_ptr : arrow_type ((memory_region:Type)::nil) (M val64_t)) (DList.DCons c (DList.DNil _))).
    {
      eapply correct_statement_call with (has_cast := false).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - (* TODO *)
Admitted.



End Check_mem_aux.
