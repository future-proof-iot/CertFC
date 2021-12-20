From compcert Require Import Coqlib Clight Integers Ctypes.
From bpf.proof Require Import Clightlogic.
From Ltac2 Require Import Ltac2 Message.
From Coq Require Import List Lia ZArith.
Import ListNotations.

Lemma list_no_repet_dec : forall {A:Type} eq_dec (l:list A) H,
    list_norepet_dec eq_dec l = left H ->
    list_norepet l.
Proof.
  intros; assumption.
Qed.

Ltac list_disjoint :=
  simpl; unfold Coqlib.list_disjoint; simpl; intuition subst; try discriminate.

Ltac list_no_repet :=
     eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.


Ltac correct_function_from_body args :=
  intros; unfold args in *;
  car_cdr;
  apply correct_function_from_body;
  [
    list_disjoint |
    list_no_repet |
    list_no_repet | reflexivity | reflexivity |idtac].


Ltac get_inv_from_list VAR L :=
  match L with
  | [] => fail -1
  | (?V,?T,?P) :: ?L' =>
      match constr:(VAR = V) with
      | ?X = ?X => constr:((T,P))
      |    _    => get_inv_from_list VAR L'
      end
  end.

Ltac get_invariant VAR :=
  let E := fresh "ME" in
  let I := fresh "I" in
  let v := fresh "v" in
  let p := fresh "p" in
  let c := fresh "c" in
  match goal with
  | H : match_temp_env ?L ?LE ?ST ?M |- _ =>
      let tp := get_inv_from_list VAR L in
      match tp with
      | (?T,?P) =>
          assert (I : exists v, Maps.PTree.get VAR LE = Some v /\
                              P v ST M /\ Cop.val_casted v T);
          [
            unfold match_temp_env in H;
            rewrite Forall_forall in H;
            assert (E : match_elt ST M LE (VAR,T,P)) by (apply H ; simpl; tauto);
            unfold match_elt,fst in E;
            destruct (Maps.PTree.get VAR LE);[|tauto];
            eexists ; split ; auto
          | destruct I as (v &p &c)]
      end
  end.

Ltac correct_body :=
  intros st le m;
(*  match type of a with
  | DList.t _ ?A =>
      unfold A in a
  end;
  car_cdr ;*)  unfold list_rel_arg,app;
  match goal with
    |- correct_body _ _ _ _ ?B _ ?INV
                 _ _ _ _ =>
      let I := fresh "INV" in
      set (I := INV) ; simpl in I;
      let B1 := eval simpl in B in
        change B with B1
  end.


Ltac exec_seq_of_labeled_statement :=
  match goal with
  | |- context[seq_of_labeled_statement ?X] =>
      let x := (eval simpl in (seq_of_labeled_statement X)) in
      change (seq_of_labeled_statement X) with x; try simpl
  end.

(**copy from cpdt *)
Ltac completer :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro
           | [ H: exists v, ?P |- _ ] => destruct H

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => specialize (H X H')
         end.

Ltac deref_loc_tactic :=
  match goal with
  | |- deref_loc ?t _ _ _ _ =>
    let r := eval compute in (access_mode t) in
      match r with
      | By_value _ => eapply deref_loc_value
      | By_reference => eapply deref_loc_reference
      | By_copy => eapply deref_loc_copy
      | By_nothing => fail "deref_loc nothing (this tactic only works on coq-compcert-32)"
      end
  end.

Ltac assign_loc_tactic :=
  match goal with
  | |- assign_loc _ ?t _ _ _ _ _ =>
    let r := eval compute in (access_mode t) in
    match r with
    | By_value _ => eapply assign_loc_value
    | By_copy => eapply assign_loc_copy
    | _ => fail "assign_loc error (this tactic only works on coq-compcert-32)"
    end
  end.

Ltac forward_eval_expr :=
  match goal with
  | |- eval_lvalue  _ _ _ _ ?e _ _ =>
    match e with
    | Evar ?id _ =>
      let r := eval compute in (Maps.PTree.get id e) in
      match r with
      | Some _ => eapply eval_Evar_local; (reflexivity || fail "Please use `eapply eval_Evar_local` to debug")
      | None => eapply eval_Evar_global; [reflexivity | reflexivity]
      end
    | Ederef _ _ =>
      eapply eval_Ederef; forward_eval_expr
    | Efield ?a _ _ =>
      let r := eval compute in (typeof a) in
      match r with
      | Tstruct _ _ =>
        eapply eval_Efield_struct; [forward_eval_expr | reflexivity | reflexivity | reflexivity]
      | Tunion _ _ =>
        eapply eval_Efield_union; [forward_eval_expr | reflexivity | reflexivity | reflexivity]
      | _ => fail "eval_lvalue fails"
      end
    end
  | |- eval_expr _ _ _ _ ?e _ =>
    match e with
    | Econst_int _ _    => econstructor; eauto
    | Econst_float _ _  => econstructor; eauto
    | Econst_single _ _ => econstructor; eauto
    | Econst_long _ _   => econstructor; eauto
    | Etempvar _ _      => eapply eval_Etempvar; reflexivity
    | Eaddrof _ _       => eapply eval_Eaddrof; forward_eval_expr
    | Eunop _ _ _       => eapply eval_Eunop; [forward_eval_expr | unfold Cop.sem_unary_operation; simpl; try reflexivity]
    | Ebinop _ _ _ _    => eapply eval_Ebinop; [forward_eval_expr | forward_eval_expr | unfold Cop.sem_binary_operation; simpl; try reflexivity]
    | Ecast _ _         => eapply eval_Ecast; [forward_eval_expr | unfold Cop.sem_cast, Cop.classify_cast; simpl; try reflexivity]
    | Esizeof _ _       => econstructor; eauto
    | Ealignof _ _      => econstructor; eauto
    | _                 => eapply eval_Elvalue; [idtac | deref_loc_tactic]
    end
  end.

Ltac forward_expr :=
  match goal with
  | |- eval_expr _ _ _ _ _ _ =>
    repeat (econstructor; eauto; try deref_loc_tactic); try reflexivity
  end.

Ltac forward_clight_ss :=
  (* repeat *)
  match goal with
  (** forward_return_some *)
  | |- Smallstep.step _ _ (State _ (Sreturn (Some _)) _ _ _ _) _ _ =>
      eapply step_return_1;[
      (** eval_expr e le m a v  *)
      forward_expr |
      (*** sem_cast v (typeof a) f.(fn_return) m = Some v' *)
      try reflexivity |
      (* Mem.free_list m (blocks_of_env e) = Some m' *)
      try reflexivity
      ]
  (** forward_return_none *)
  | |- Smallstep.step _ _ (State _ (Sreturn None) _ _ _ _) _ _ =>
      eapply step_return_0; try reflexivity
    (** assign *)
  | |- Smallstep.step _ _ (State _ (Sassign _ _ ) _ _ _ _) _ _ =>
      repeat (econstructor; eauto; try deref_loc_tactic)
    (** set *)
  | |- Smallstep.step _ _ (State _ (Sset _ _) _ _ _ _) _ _ =>
      eapply step_set; forward_expr
    (** seq *)
  | |- Smallstep.step _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply step_seq
  | |- Smallstep.step _ _ (State _ Sskip (Kseq _ _) _ _ _ ) _ _ =>
      eapply step_skip_seq
  | |- Smallstep.step _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
      eapply step_ifthenelse;[
        (** eval_expr e le m a v1 *)
        forward_expr |
        try reflexivity
        (** bool_val v1 (typeof a) m = Some b *)
      ]
    (** switch *)
  | |- Smallstep.step _ _ (State _ (Sswitch _ _) _ _ _ _) _ _ =>
      eapply step_switch; [
        (** eval_expr e le m a v *)
        forward_expr |
        (** sem_switch_arg v (typeof a) = Some n *)
        try reflexivity
      ]; try exec_seq_of_labeled_statement

    (** call *)
  | |- Smallstep.step _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply step_call; [
        (** classify_fun (typeof a) = fun_case_f tyargs tyres cconv *)
        reflexivity |
        (** eval_expr e le m a vf *)
        idtac (* TODO *) |
        (**  eval_exprlist e le m al tyargs vargs *)
        idtac (* TODO *) |
        (** Genv.find_funct ge vf = Some fd *)
        reflexivity (**r or `econstructor; eauto`, which one is better *) |
        (** type_of_fundef fd = Tfunction tyargs tyres cconv *)
        reflexivity
      ]
  end.

Ltac forward_clight :=
  (* repeat *)
  match goal with
  (** forward_return_some *)
  | |- step _ _ (State _ (Sreturn (Some _)) _ _ _ _) _ _ =>
      eapply step_return_1;[
      (** eval_expr e le m a v  *)
      forward_expr |
      (*** sem_cast v (typeof a) f.(fn_return) m = Some v' *)
      try reflexivity |
      (* Mem.free_list m (blocks_of_env e) = Some m' *)
      try reflexivity
      ]
  (** forward_return_none *)
  | |- step _ _ (State _ (Sreturn None) _ _ _ _) _ _ =>
      eapply step_return_0; try reflexivity
    (** assign *)
  | |- step _ _ (State _ (Sassign _ _ ) _ _ _ _) _ _ =>
      repeat (econstructor; eauto; try deref_loc_tactic)
    (** set *)
  | |- step _ _ (State _ (Sset _ _) _ _ _ _) _ _ =>
      eapply step_set; forward_expr
    (** seq *)
  | |- step _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply step_seq
  | |- step _ _ (State _ Sskip (Kseq _ _) _ _ _ ) _ _ =>
      eapply step_skip_seq
  | |- step _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
      eapply step_ifthenelse;[
        (** eval_expr e le m a v1 *)
        forward_expr |
        try reflexivity
        (** bool_val v1 (typeof a) m = Some b *)
      ]
    (** switch *)
  | |- step _ _ (State _ (Sswitch _ _) _ _ _ _) _ _ =>
      eapply step_switch; [
        (** eval_expr e le m a v *)
        forward_expr |
        (** sem_switch_arg v (typeof a) = Some n *)
        try reflexivity
      ]; try exec_seq_of_labeled_statement

    (** call *)
  | |- step _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply step_call; [
        (** classify_fun (typeof a) = fun_case_f tyargs tyres cconv *)
        reflexivity |
        (** eval_expr e le m a vf *)
        idtac (* TODO *) |
        (**  eval_exprlist e le m al tyargs vargs *)
        idtac (* TODO *) |
        (** Genv.find_funct ge vf = Some fd *)
        reflexivity (**r or `econstructor; eauto`, which one is better *) |
        (** type_of_fundef fd = Tfunction tyargs tyres cconv *)
        reflexivity
      ]
  end.


Ltac forward_star :=
  unfold step2;
  match goal with
  (** Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s *)
  | |- Smallstep.star _  _ ?s1 _ ?s2 =>
    let res1 := (eval simpl in s1) in
    let res2 := (eval simpl in s2) in
      match res1 with
      | Returnstate _ _ _ =>
        match res2 with
        | Returnstate _ _ _ =>
          (eapply Smallstep.star_refl || fail "debug `eapply Smallstep.star_refl`")
        | _ => eapply Smallstep.star_step; eauto
        end
      | _ => eapply Smallstep.star_step; eauto
      end (*
  | |- Smallstep.star _  _ ?s _ ?s =>
    eapply Smallstep.star_refl
  | |- Smallstep.star _  _ (Returnstate _ _ _) _ (Returnstate _ _ _) =>
    (eapply Smallstep.star_refl || fail "debug `eapply Smallstep.star_refl`")
  (** 
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3. *)
  | |- Smallstep.star _ _ _ _ _ =>
    eapply Smallstep.star_step; eauto *)
  | |- Smallstep.step _ _ _ _ _ =>
      forward_clight_ss
  | |- step _ _ _ _ _ =>
      forward_clight
  | |- Events.E0 = Events.Eapp _ _ =>
      try reflexivity
  end.

Ltac forward_plus :=
 match goal with
  (** forward_seq *)
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | try simpl ..]
  (** forward_call_one_arg *)
  | |- Smallstep.plus _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto;
      [eapply step_call;
        [reflexivity |                                (** goal: classify_fun *)
         eapply eval_Elvalue;                         (** goal: eval_expr *)
          [eapply eval_Evar_global; reflexivity |     (** eval_lvalue *)
           eapply deref_loc_reference; reflexivity] | (** goal: deref_loc *)
         eapply eval_Econs;                           (** goal: eval_exprlist *)
          [eapply eval_Etempvar; reflexivity |        (** goal: eval_expr *)
           reflexivity |                              (** goal: Cop.sem_cast *)
           eapply eval_Enil] |                        (** goal: eval_exprlist *)
         econstructor; eauto |                        (** goal: Globalenvs.Genv.find_funct *)
         reflexivity] |                               (** goal: type_of_fundef *)
       try simpl ..]
  (** forward_returnstate *)
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | try simpl ..]
  (** forward_skip_seq *)
  | |- Smallstep.plus _ _ (State _ Sskip _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | try simpl ..]
  (** forward_if *)
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
    [eapply step_ifthenelse;
      [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity |
       reflexivity] |
     try simpl ..]
  (** forward_return_some *)
  | |- Smallstep.plus _ _ (State _ (Sreturn (Some _)) _ _ _ _) _ _ =>
    eapply Smallstep.plus_one; eauto;
      [eapply step_return_1 | try simpl ..] (*
    eapply Smallstep.plus_left'; eauto;
      [eapply step_return_1;
        [eapply eval_Econst_long |
         reflexivity |
         reflexivity] | try simpl ..]*)
  (** forward_return_none *)
  | |- Smallstep.plus _ _ (State _ (Sreturn None) _ _ _ _) _ _ =>
      eapply Smallstep.plus_one; eauto; eapply step_return_0; try reflexivity
 end.

Ltac prepare :=
  match goal with
  | |- correct_function3 _ ?args _ _ _ _ _ _ _ =>
    eapply correct_function_from_body;
    [ simpl; unfold Coqlib.list_disjoint; simpl; intuition (subst; discriminate) |
      eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
      simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
      reflexivity |
      reflexivity |
      idtac
    ];
    intros;
    unfold args in *;
    car_cdr;
    unfold list_rel_arg;
    simpl;
    unfold correct_body;
    repeat intro
  end.

(**
match_temp_env
      [(_x, Clightdefs.tulong, stateless val64_correct c);
      (_y, Clightdefs.tulong, stateless val64_correct c0)] le st
      m
*)

Ltac get_invariant_more VAR :=
  let E := fresh "ME" in
  let I := fresh "I" in
  let v := fresh "v" in
  let p := fresh "p" in
  let c := fresh "c" in
  match goal with
  | H : match_temp_env ?L ?LE ?ST ?M |- _ =>
      let tp := get_inv_from_list VAR L in
      match tp with
      | (?T,?P) =>
          assert (I : exists v, Maps.PTree.get VAR LE = Some v /\
                              P v ST M /\ Cop.val_casted v T);
          [
            unfold match_temp_env in H;
            rewrite Forall_forall in H;
            assert (E : match_elt ST M LE (VAR,T,P)) by (apply H ; simpl; tauto);
            unfold match_elt,fst in E;
            destruct (Maps.PTree.get VAR LE);[|tauto];
            eexists ; split ; auto
          | destruct I as (v &p &c)]; completer
      end
  end.

(** Integer.max_unsigned *)

Lemma Int_max_unsigned_eq64:
  Int.max_unsigned = 4294967295%Z.
Proof.
  Transparent Archi.ptr64.
  unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize.
  reflexivity.
Qed.

Lemma Int_eq_one_zero :
  Int.eq Int.one Int.zero = false.
Proof.
  reflexivity.
Qed.

Lemma Ptrofs_max_unsigned_eq32:
  Ptrofs.max_unsigned = 4294967295%Z.
Proof.
  unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  Transparent Archi.ptr64.
  reflexivity.
Qed.

