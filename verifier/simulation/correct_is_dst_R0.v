From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.comm Require Import Monad.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic CorrectRel.
From bpf.verifier.comm Require Import monad.

From bpf.verifier.synthesismodel Require Import verifier_synthesis.
From bpf.verifier.clightmodel Require Import verifier.
From bpf.verifier.simulation Require Import VerifierSimulation VerifierRel.


(**
Check is_dst_R0.
is_dst_R0
     : int64 -> M bool
*)

Section Is_dst_R0.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := is_dst_R0.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_is_dst_R0.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (int64_correct x)) (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x  => StateLess _ (bool_correct x).

  Instance correct_function_is_dst_R0 : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _i.
    unfold eval_inv, int64_correct in c0.
    subst.

    eexists; exists m, Events.E0.

    split_and; auto.
    {
      forward_star.
      simpl.
      match goal with
      | |- Cop.sem_cast ?X _ _ _ = _ =>
        instantiate (1:= X)
      end.
      unfold Cop.sem_cast, Val.of_bool; simpl.
      unfold Vtrue, Vfalse.
      destruct Int.eq.
      rewrite Int_eq_one_zero.
      reflexivity.
      rewrite Int.eq_true.
      reflexivity.
      forward_star.
    }
    unfold eval_inv, match_res, state.is_dst_R0'.
    unfold bool_correct, Val.of_bool, BinrBPF.get_dst.
    unfold Vtrue, Vfalse, Int.cmpu.
    destruct Int.eq; reflexivity.
    unfold Val.of_bool.
    unfold Vtrue, Vfalse.
    destruct Int.eq; constructor; reflexivity.
    apply unmodifies_effect_refl.
  Qed.

End Is_dst_R0.

Existing  Instance correct_function_is_dst_R0.
