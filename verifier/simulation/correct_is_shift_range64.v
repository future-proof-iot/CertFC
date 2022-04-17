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
Check is_shift_range64.
is_shift_range64
     : int64 -> M bool
*)

Section Is_shift_range64.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type); (int:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := is_shift_range64.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_is_shift_range64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (int64_correct x))
        (dcons (fun x => StateLess _ (int32_correct x))
          (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x  => StateLess _ (bool_correct x).

  Instance correct_function_is_shift_range64 : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _i.
    get_invariant _upper.
    unfold eval_inv, int64_correct in c1.
    unfold eval_inv, int32_correct in c2.
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
      match goal with
      | |- _ = Some (if ?X then _ else _) =>
        destruct X; [ rewrite Int_eq_one_zero | rewrite Int.eq_true]; reflexivity
      end.
      forward_star.
    }
    unfold eval_inv, match_res, state.is_shift_range64'.
    unfold bool_correct, Val.of_bool, BinrBPF.get_immediate.
    unfold Vtrue, Vfalse, Int.cmpu, rBPFValues.int64_to_sint32.
    match goal with
    | |- (if ?X then _ else _) = _ =>
      destruct X; reflexivity
    end.
    unfold Val.of_bool.
    unfold Vtrue, Vfalse.
    match goal with
    | |- Cop.val_casted (if ?X then _ else _) _ =>
      destruct X; constructor; reflexivity
    end.
    apply unmodifies_effect_refl.
  Qed.

End Is_shift_range64.

Existing  Instance correct_function_is_shift_range64.
