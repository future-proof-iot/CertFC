From bpf.comm Require Import Regs State Monad.
From bpf.src Require Import DxIntegers DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check get_dst.
get_dst
     : int64_t -> M reg

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

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_dst.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless reg_int64_correct)
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => reg_correct x v.

  Instance correct_function3_get_dst : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _ins.

    unfold stateless, reg_int64_correct in H0.
    destruct H0 as (Hv_eq & (Hreg_range_0 & Hreg_range10)).
    subst.

    (**according to the type:
         static unsigned int get_dst(unsigned long long ins1)
       1. return value should be  
       2. the memory is same
     *)
    unfold int64_to_dst_reg.
    unfold z_to_reg, Regs.get_dst.
    simpl in c.
    exists (Vint (Int.repr (Int64.unsigned (Int64.shru (Int64.and c (Int64.repr 4095)) (Int64.repr 8))))), m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.
    -
      unfold match_res.
      unfold reg_correct. (**r we need the invariant reg \in [0; 10] *)
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
