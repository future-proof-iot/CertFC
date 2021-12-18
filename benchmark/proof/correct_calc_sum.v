From bpf.src Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.benchmark Require Import clightlogicexample BenchmarkTests.

Locate nat_correct.

(**
unsigned int calc_sum(unsigned int v, unsigned int n)
{
  unsigned int n1;
  unsigned int nv;
  if (n == 0U) {
    return 0U;
  } else {
    n1 = n - 1U;
    nv = get_add(v, 1U);
    return calc_sum(nv, n1);
  }
}

Print calc_sum.
calc_sum = 
fix calc_sum (v : valu32_t) (n : nat) {struct n} : M valu32_t :=
  match n with
  | 0 => returnM val32_zero
  | S n1 => bindM (get_add v val32_one) (fun nv : valu32_t => calc_sum nv n1)
  end
     : valu32_t -> nat -> M valu32_t

*)

Section Calc_sum.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(valu32_t:Type); (nat:Type)].
  Definition res : Type := (valu32_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := calc_sum.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_calc_sum.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless valu32_correct)
       (DList.DCons (stateless nat_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => valu32_correct x v.

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

  Lemma calc_sum_eq :  forall n v,
      calc_sum v n =
        if Nat.eqb n 0 then returnM val32_zero
        else bindM (get_add v val32_one) (fun nv : valu32_t => calc_sum nv (Nat.pred n)).
  Proof.
    destruct n.
    - simpl. auto.
    - intros.
      simpl. reflexivity.
  Qed.

  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

  Lemma mod_eq : forall (x y:Z), (x >= 0 -> y > 0 -> x mod y = x -> x < y)%Z.
  Proof.
    intros.
    zify.
    intuition subst ; try lia.
  Qed.



  Instance correct_function3_calc_sum : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    intros. unfold args in a.
    car_cdr.
    revert c.
    induction c0.
    { intros.
      correct_function_from_body.
      correct_body.
      repeat intro.
      unfold INV in H.
      get_invariant_more _v.
      get_invariant_more _n.
      unfold stateless, valu32_correct in H1.
      unfold stateless, nat_correct in H3.
      destruct H1 as (Hc_eq & (vi & Hvi_eq)).
      destruct H3 as (H3 & _).
      subst.
      eexists. exists m, Events.E0.
      repeat split.
      + eapply Smallstep.star_step.
        econstructor;eauto.
        econstructor ; eauto.
        econstructor;eauto.
        econstructor ; eauto.
        econstructor ; eauto.
        simpl. reflexivity.
        change (negb (Int.eq Int.one Int.zero)) with true.
        simpl.
        eapply Smallstep.star_step.
        econstructor;eauto.
        econstructor ; eauto.
        econstructor;eauto.
        econstructor ; eauto.
        econstructor ; eauto.
        reflexivity.
        reflexivity.
      + eexists. reflexivity.
      + econstructor;eauto.
    }
    { intros.
      correct_function_from_body.
      correct_body.
      unfold f. unfold app.
      rewrite calc_sum_eq.
      eapply correct_statement_if_body_expr.
      simpl.
      apply correct_statement_seq_set with (match_res1 := fun _ => stateless nat_correct c0).
      +
        intros.
        unfold INV in H.
        get_invariant_more _n.
        unfold stateless,nat_correct in H0.
        destruct H0 ; subst.
        eexists.
        repeat split.
        unfold exec_expr.
        rewrite p0.
        unfold Cop.sem_binary_operation.
        unfold Cop.sem_sub. simpl.
        unfold Cop.sem_binarith.
        simpl. unfold Cop.sem_cast.
        unfold Cop.classify_cast.
        simpl.
        {
          destruct Archi.ptr64.
          - repeat f_equal.
            simpl.
            simpl in H2.
            unfold Int.sub.
            rewrite H2. f_equal.
            change (Int.unsigned (Int.repr 1))%Z with 1%Z.
            lia.
          - repeat f_equal.
            simpl.
            simpl in H2.
            unfold Int.sub.
            rewrite H2. f_equal.
            change (Int.unsigned (Int.repr 1))%Z with 1%Z.
            lia.
        }
        rewrite Int.unsigned_repr_eq.
        apply Z.mod_small.
        rewrite Int.unsigned_repr_eq in H2.
        apply mod_eq in H2.
        lia.
        lia.
        unfold Int.modulus.
        reflexivity.
        simpl.
        constructor.
        reflexivity.
      + unfold INV.
        simpl. intuition subst ; discriminate.
      + intros.
        eapply correct_statement_seq_body;eauto.
        unfold typeof.
        change (get_add c val32_one) with
          (app (get_add: arrow_type (valu32_t :: valu32_t :: nil) (M valu32_t))
                           (DList.DCons c
                                                            (DList.DCons val32_one (DList.DNil _)))).
        eapply correct_statement_call with (has_cast:=false).
        reflexivity.
        reflexivity.
        reflexivity.
        intros.
        admit.
        admit.
        reflexivity.
        reflexivity.
        reflexivity.
        unfold INV.
        simpl. intuition subst ; discriminate.
        simpl. intuition subst ; discriminate.
        reflexivity.
        instantiate (1:= true).
        reflexivity.
        admit.
        intros.
        unfold typeof.
        change (calc_sum x0 c0) with
          (app (calc_sum: arrow_type (valu32_t :: (nat:Type) :: nil) (M valu32_t))
               (DList.DCons x0
                            (DList.DCons c0 (DList.DNil _)))).
        eapply correct_body_call_ret with (has_cast := false);eauto.
        reflexivity.
        reflexivity.
        reflexivity.
        admit.
        admit.
      +  simpl.
        reflexivity.
      + intros. unfold INV in H.
        get_invariant_more _n.
        unfold stateless,nat_correct in H0.
        intuition subst.
        unfold exec_expr.
        rewrite p0.
        simpl. unfold Cop.sem_cmp.
        unfold Cop.classify_cmp.
        simpl.
        unfold Cop.sem_binarith.
        simpl.
        unfold Cop.sem_cast.
        simpl.
        destruct (Int.eq (Int.repr (Z.pos (Pos.of_succ_nat c0))) (Int.repr 0)) eqn:E; auto.
        exfalso.
        apply Int.same_if_eq in E.
        apply (f_equal Int.unsigned) in E.
        simpl in H3.
        rewrite H3 in E.
        change (Int.unsigned (Int.repr 0)) with 0%Z in E.
        lia.
        destruct Archi.ptr64.
        simpl. rewrite E. reflexivity.
        rewrite E. reflexivity.
  Admitted.


    (**r
      H2 :         Vint (Int.repr (Z.of_nat (S c0))) = v0
      Ihc0: ... -> Vint (Int.repr (Z.of_nat c0)) = v0 -> ...
    *)

    (**according to the c function:
unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}
       1. return value should be  x+y
       2. the memory is same
      *)
    destruct (calc_sum _ _ _) eqn: Heq; [idtac | apply I].
    unfold calc_sum in Heq.
    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_one; eauto.
      eapply step_return_1.
      +
        repeat econstructor; eauto.
        Transparent Archi.ptr64.
        unfold Cop.sem_binary_operation.
        unfold Cop.sem_add, Cop.classify_add, Ctypes.typeconv; simpl.
        unfold Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast; simpl.
        reflexivity.
      + econstructor; eauto.
      + reflexivity.
    - simpl.
      exists (Int.add vi vj); reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Calc_sum.

Existing Instance correct_function3_calc_sum.
