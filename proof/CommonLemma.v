From compcert Require Import Coqlib Clight Integers Values Ctypes Memory AST.
From bpf.comm Require Import Regs State.
From bpf.proof Require Import Clightlogic CommonLib.
From Coq Require Import List Lia ZArith.
Import ListNotations.

Open Scope Z_scope.

Ltac correct_Forall :=
match goal with
| H: Forall (match_elt ?st ?m ?le) ?L |- _ =>
  change (match_temp_env L le st m) in H
end.

Ltac my_reflex :=
  match goal with
  | |- ?X = Some _ =>
      let x := (eval compute in X) in
      replace X with x by reflexivity;
      reflexivity
  end.

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


  Ltac IN T :=
    lazymatch T with
    | In ?X nil => fail -1 "Fail to get a membership proof"
    | In ?X (cons ?X ?L') => constr:(@in_eq _ X L')
    | In ?X (cons ?Y ?L') =>
        let inr := constr:(In X L') in
        let prf := IN inr in
        constr:(@in_cons _ Y X _ prf)
    |  ?T        => fail -1 "list is not of the form  a1::....::an:nil" T
    end.

    Ltac get_invariant VAR :=
  let E := fresh "ME" in
  let I := fresh "I" in
  let v := fresh "v" in
  let p := fresh "p" in
  let c := fresh "c" in
  let v1 := fresh "v1" in
  match goal with
  | H:match_temp_env ?L ?LE ?ST ?M
    |- _ =>
        let tp := get_inv_from_list VAR L in
        match tp with
        | (?T, ?P) =>
            assert (I : exists v, Maps.PTree.get VAR LE = Some v /\ P v ST M /\ Cop.val_casted v T);
             [ unfold match_temp_env in H; rewrite Forall_forall in H;
               assert (E : match_elt ST M LE (VAR, T, P));
                [ (apply H; unfold AST.ident;
                   match goal with
                         |- ?G => let prf := IN G in exact prf
                   end)  |
               unfold match_elt, fst,snd in E; destruct (Maps.PTree.get VAR LE) as [v1|]
               ; [
                 exists v1 ; split ;[reflexivity | exact E]
               | (exfalso ; assumption) ]]
             | destruct I as (v, (p, (c, _))) ]
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

Ltac forward_smallstep :=
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

Lemma Int_eq_one_zero :
  Int.eq Int.one Int.zero = false.
Proof.
  reflexivity.
Qed.

Ltac simpl_if_one_zero :=
  match goal with
  | |- context[if negb (Int.eq Int.one Int.zero) then _ else _ ] =>
    rewrite Int_eq_one_zero; unfold negb
  | |- context[if Int.eq Int.one Int.zero then _ else _ ] =>
    rewrite Int_eq_one_zero
  | |- context[if negb (Int.eq Int.zero Int.zero) then _ else _ ] =>
    rewrite Int.eq_true; unfold negb
  | |- context[(if Int.eq Int.zero Int.zero then _ else _)] =>
    rewrite Int.eq_true
  end.

Ltac forward_star' :=
  (*unfold step2; *)
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
      end
  | |- Events.E0 = Events.Eapp _ _ =>
      try reflexivity
  end.

Ltac forward_step' :=
  (*unfold step2; *)
  match goal with
  | |- Smallstep.step _ _ _ _ _ =>
      forward_smallstep
  | |- step _ _ _ _ _ =>
      forward_clight
  | |- Events.E0 = Events.Eapp _ _ =>
      try reflexivity
  end.

Ltac post_process :=
  match goal with
  | |- Maps.PTree.get ?X (Maps.PTree.set ?X _ _) = Some _ =>
      rewrite Maps.PTree.gss
  | H: Maps.PTree.get ?X _ = Some _ |- Maps.PTree.get ?X (Maps.PTree.set ?Y _ _) = Some _ =>
    let Heq := fresh "Heq" in
      rewrite Maps.PTree.gso; try (apply H); try (unfold X, Y; intro Heq; inversion Heq)
  end; try simpl_if_one_zero.


Ltac forward_star := try simpl_if_one_zero; try forward_star'; repeat forward_step'; try post_process; try reflexivity.

(** Integer.max_unsigned *)

Lemma Int_max_unsigned_eq64:
  Int.max_unsigned = 4294967295%Z.
Proof.
  Transparent Archi.ptr64.
  unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize.
  reflexivity.
Qed.

Lemma Ptrofs_max_unsigned_eq32:
  Ptrofs.max_unsigned = 4294967295.
Proof.
  unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  Transparent Archi.ptr64.
  reflexivity.
Qed.

Lemma Int_unsigned_ge_zero :
  forall i,
    Int.unsigned i >= 0.
Proof.
  intro.
  assert (Hrange: 0 <= Int.unsigned i <= Int.max_unsigned). { apply Int.unsigned_range_2. }
  destruct Hrange.
  (**r Search (_ <= _). *)
  apply Z.le_ge in H.
  assumption.
Qed.

Lemma Ptrofs_unsigned_ge_zero :
  forall i,
    Ptrofs.unsigned i >= 0.
Proof.
  intro.
  assert (Hrange: 0 <= Ptrofs.unsigned i <= Ptrofs.max_unsigned). { apply Ptrofs.unsigned_range_2. }
  destruct Hrange.
  (**r Search (_ <= _). *)
  apply Z.le_ge in H.
  assumption.
Qed.

Lemma Ptrofs_unsigned_repr_n:
  forall n,
  0 <= n <= 4294967295 ->
  Ptrofs.unsigned (Ptrofs.repr n) = n.
Proof.
  intros.
  rewrite Ptrofs.unsigned_repr; [reflexivity | rewrite Ptrofs_max_unsigned_eq32; lia].
Qed.

Lemma Int_unsigned_repr_n:
  forall n,
  0 <= n <= 4294967295 ->
  Int.unsigned (Int.repr n) = n.
Proof.
  intros.
  rewrite Int.unsigned_repr; [reflexivity | rewrite Int_max_unsigned_eq64; lia].
Qed.

Lemma Ptrofs_unsigned_repr_id_of_reg:
  forall r,
  Ptrofs.unsigned (Ptrofs.repr (8 * id_of_reg r)) = 8 * id_of_reg r.
Proof.
  intros.
  unfold id_of_reg; destruct r;
  rewrite Ptrofs.unsigned_repr; try rewrite Ptrofs_max_unsigned_eq32; try lia.
Qed.

Lemma Ptrofs_unsigned_repr_id_of_reg_8:
  forall r,
  0 <= (8 + 8 * id_of_reg r) <= Ptrofs.max_unsigned.
Proof.
  intros.
  unfold id_of_reg; destruct r;
  rewrite Ptrofs_max_unsigned_eq32; try lia.
Qed.

Lemma eval_upd_regmap_same:
  forall r regs v, eval_regmap r (upd_regmap r v regs) = v.
Proof.
  intros.
  unfold eval_regmap, upd_regmap.
  destruct r; reflexivity.
Qed.

Lemma eval_upd_regmap_other:
  forall r0 r1 regs v,
    r0 <> r1 -> 
      eval_regmap r0 (upd_regmap r1 v regs) = eval_regmap r0 regs.
Proof.
  intros.
  unfold eval_regmap, upd_regmap.
  destruct r0; destruct r1; try reflexivity.
  all: exfalso; apply H; reflexivity.
Qed.

Lemma Hreg_eq: 
  forall r, (Ptrofs.unsigned
              (Ptrofs.repr
                 (Ptrofs.unsigned (Ptrofs.repr 8) +
                  Ptrofs.unsigned (Ptrofs.repr (8 * id_of_reg r))))) = (8 + 8 * id_of_reg r)%Z.
Proof.
  intros.
  repeat rewrite Ptrofs.unsigned_repr; try (rewrite Ptrofs_max_unsigned_eq32; unfold id_of_reg; destruct r; lia).
  reflexivity.
Qed.

Lemma nth_error_some_length:
  forall A n l (m:A), nth_error l n = Some m -> (0 <= n < List.length l)%nat.
Proof.
  intros.
  rewrite <- nth_error_Some.
  split; intros.
  - lia.
  - destruct n.
    + simpl in *.
      destruct l.
      inversion H.
      intro.
      inversion H0.
    + simpl in *.
      destruct l.
      inversion H.
      rewrite H.
      intro H0; inversion H0.
Qed.
(*
Section Test.
  Variable A: Type.
  Parameter testP: nat -> A -> Prop.
  Fixpoint list_dualP (ofs: nat) (l:list A) :=
  match l with
  | nil => True
  | hd :: l' => testP (16 * ofs) hd /\ list_dualP (ofs+1) l'
  end.
  Lemma list_dual_in :
    forall l mr ofs
    (Hin : In mr l)
    (Hlist : list_dualP ofs l),
      exists n, testP (16 * n) mr.
  Proof.
    intros.
    induction l.
    - simpl in Hin. inversion Hin.
    - simpl in Hin. destruct Hlist as (Hlist0 & Hlist1).
      destruct Hin.
      + subst. exists ofs; assumption.
      + apply IHl. assumption.
        admit.
  Admitted.
  Variable default_A: A.
  Definition list_dualP' (ofs: nat) (l:list A) :=
    forall n, (0 <= n < List.length l)%nat -> testP (16 * ofs) (nth n l default_A).
  Lemma list_dual_in' :
    forall l mr ofs
    (Hin : In mr l)
    (Hlist : list_dualP' ofs l),
      exists n, testP (16 * n) mr.
  Proof.
    intros.
    apply In_nth_error in Hin.
    destruct Hin as (n & Hin).
    apply nth_error_some_length in Hin as Hlen.
    unfold list_dualP' in Hlist.
    specialize (Hlist n Hlen).
    destruct Hlen as ( _ & Hlen).
    apply nth_error_nth' with (d:= default_A) in Hlen.
    rewrite Hlen in Hin.
    inversion Hin.
    subst.
    exists ofs; assumption.
  Qed.
End Test. *)

Lemma valid_access_chunk_implies:
  forall m chunk b ofs p,
    Mem.valid_access m chunk b ofs p -> Mem.valid_access m Mint8unsigned b ofs p.
Proof.
  intros.
  destruct chunk.
  all: unfold Mem.valid_access in *;
    destruct H as (Hrange & Halign);
    split; [unfold size_chunk, Mem.range_perm in *; intros; apply Hrange; lia | unfold align_chunk; apply Z.divide_1_l].
Qed.

Close Scope Z_scope.
