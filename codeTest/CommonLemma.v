From compcert Require Import Coqlib Clight.
From bpf.proof Require Import Clightlogic.

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


Ltac correct_function_from_body :=
  apply correct_function_from_body;
  [
    list_disjoint |
    list_no_repet |
    list_no_repet | reflexivity | reflexivity |idtac].


Ltac get_inv_from_list VAR L :=
  match L with
  | nil => fail -1
  | cons (?V,?T,?P) ?L' =>
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
  intros st le m a;
  match type of a with
  | DList.t _ ?A =>
      unfold A in a
  end;
  car_cdr ; unfold list_rel_arg,app;
  match goal with
    |- correct_body _ _ _ _ ?B _ ?INV
                 _ _ _ _ =>
      let I := fresh "INV" in
      set (I := INV) ; simpl in I;
      let B1 := eval simpl in B in
        change B with B1
  end.



(*
Ltac forward_seq :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | idtac]
  end.

Ltac forward_call_one_arg :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_call; [reflexivity | eapply eval_Elvalue;[eapply eval_Evar_global; reflexivity | eapply deref_loc_reference; reflexivity] | eapply eval_Econs; [eapply eval_Etempvar; reflexivity | reflexivity | eapply eval_Enil] | econstructor; eauto | reflexivity] | idtac]
  end.

Ltac forward_returnstate :=
  match goal with
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | idtac]
  end.

Ltac forward_skip_seq :=
  match goal with
  | |- Smallstep.plus _ _ (State _ Sskip (Kseq _ _) _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | idtac]
  end.

Ltac forward_if :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
  eapply Smallstep.plus_left'; eauto; [eapply step_ifthenelse; [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity | reflexivity] | idtac]
  end.*)

Ltac eforward_plus :=
 match goal with
  (** forward_seq *)
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | idtac]
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
       idtac]
  (** forward_returnstate *)
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | idtac]
  (** forward_skip_seq *)
  | |- Smallstep.plus _ _ (State _ Sskip (Kseq _ _) _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | idtac]
  (** forward_if *)
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
    [eapply step_ifthenelse;
      [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity |
       reflexivity] |
     idtac]
  (** forward_return_some *)
  | |- Smallstep.plus _ _ (State _ (Sreturn _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
      [eapply step_return_1;
        [eapply eval_Econst_long |
         reflexivity |
         reflexivity] | idtac]
 end.

Ltac forward_plus :=
 match goal with
  (** forward_seq *)
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | idtac | simpl]
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
       idtac | simpl]
  (** forward_returnstate *)
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | idtac | simpl]
  (** forward_skip_seq *)
  | |- Smallstep.plus _ _ (State _ Sskip (Kseq _ _) _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | idtac | simpl]
  (** forward_if *)
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
    [eapply step_ifthenelse;
      [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity |
       reflexivity] |
     idtac | simpl]
  (** forward_return_some *)
  | |- Smallstep.plus _ _ (State _ (Sreturn (Some _)) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
      [eapply step_return_1;
        [eapply eval_Econst_long |
         reflexivity |
         reflexivity] | idtac | simpl]
 end.

