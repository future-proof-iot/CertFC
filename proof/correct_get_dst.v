From dx.tests Require Import DxIntegers DxValues DxMemRegion DxRegs DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma interpreter.


(**

static unsigned int get_dst(unsigned long long ins1)
{
  return (unsigned int) ((ins1 & 4095LLU) >> 8LLU);
}

Definition get_dst (ins1: int64_t): M reg :=
  returnM (int64_to_dst_reg ins1).

 *)

Open Scope Z_scope.

Section Get_dst.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64_t:Type)].
  Definition res : Type := (reg:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_dst.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_dst.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless reg_int64_correct)
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => reg_correct x v.

  Instance correct_function3_get_dst : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _ins1.

    unfold stateless, reg_int64_correct in H1.
    destruct H1 as (Hv_eq & (Hreg_range_0 & Hreg_range10)).
    subst v.

    (**according to the type:
         static unsigned int get_dst(unsigned long long ins1)
       1. return value should be  
       2. the memory is same
     *)
    unfold int64_to_dst_reg.
    unfold z_to_reg, DxRegs.get_dst.
    simpl in c.
    exists (Vint (Int.repr (Int64.unsigned (Int64.shru (Int64.and c (Int64.repr 4095)) (Int64.repr 8))))), m, Events.E0.

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
        unfold Cop.sem_binary_operation.
        unfold Cop.sem_add, Cop.classify_add, Ctypes.typeconv; simpl.
        unfold Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast; simpl.
        reflexivity.
        unfold Cop.sem_cast; simpl.
        reflexivity.
      +
        unfold Cop.sem_cast; reflexivity.
      + reflexivity.
    -
      unfold match_res.
      unfold reg_correct. (**r we need the invariant reg \in [0; 10] *)
      unfold id_of_reg.
      unfold int64_0xfff, int64_8.
      remember ((Int64.unsigned (Int64.shru (Int64.and c (Int64.repr 4095)) (Int64.repr 8)))) as X.
      Ltac zeqb :=
      match goal with
      | |- context[Z.eqb ?X1 ?X2] =>
          destruct (Z.eqb X1 X2) eqn:Heq; [
      rewrite Z.eqb_eq in Heq; rewrite Heq; try reflexivity | rewrite Z.eqb_neq in Heq]
      end.
      try zeqb; rename Heq into Heq0.
      try zeqb; rename Heq into Heq1.
      try zeqb; rename Heq into Heq2.
      try zeqb; rename Heq into Heq3.
      try zeqb; rename Heq into Heq4.
      try zeqb; rename Heq into Heq5.
      try zeqb; rename Heq into Heq6.
      try zeqb; rename Heq into Heq7.
      try zeqb; rename Heq into Heq8.
      try zeqb; rename Heq into Heq9.
      assert (HZ_eq: X = 10). { lia. }
      rewrite HZ_eq; reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Get_dst.
Close Scope Z_scope.

Existing Instance correct_function3_get_dst.
