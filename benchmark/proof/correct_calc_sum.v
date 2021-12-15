From bpf.src Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.benchmark Require Import clightlogicexample BenchmarkTests.

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

  Instance correct_function3_calc_sum : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** should we induction c0 before correct_body *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _v.
    get_invariant_more _n.

    unfold stateless, valu32_correct in H0.
    unfold stateless, nat_correct in H2.
    destruct H0 as (Hc_eq & (vi & Hvi_eq)).
    subst c v.
    simpl in c0.
    (*generalize c0.*)
    induction c0.
    {
      simpl.
      intros.
      eexists. exists m, Events.E0.
      repeat split; unfold step2.
      -
        apply Smallstep.plus_star.
        eapply Smallstep.plus_left'; eauto.
        eapply step_ifthenelse.
        econstructor; eauto.
        econstructor; eauto.
        Transparent Archi.ptr64.
        econstructor; eauto.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
        rewrite <- H2. simpl.
        reflexivity.
        reflexivity.

        rewrite Int_eq_one_zero.
        unfold negb.

        forward_plus.
        econstructor; eauto.
        reflexivity.
        reflexivity.
        reflexivity.

      - eexists.
        unfold val32_zero; reflexivity.
      - constructor.
        reflexivity.
    }

    simpl; simpl in IHc0.
    unfold match_temp_env in H, IHc0.
    
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
