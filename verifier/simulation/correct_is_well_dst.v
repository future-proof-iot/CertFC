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
Check is_well_dst.
is_well_dst
     : int64 -> M bool
*)

Section Is_well_dst.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M state.state res) := is_well_dst.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_is_well_dst.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    dcons (fun x => StateLess _ (int64_correct x))
        (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv state.state := fun x  => StateLess _ (bool_correct x).

  Instance correct_function_is_well_dst : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f. unfold is_well_dst.
    correct_forward.

    get_invariant _i.
    unfold eval_inv, int64_correct in c0.
    subst.

    eexists.

    split_and; auto.
    {
      unfold exec_expr. repeat
      match goal with
      | H: ?X = _ |- context [match ?X with _ => _ end] =>
        rewrite H
      end. simpl.
      unfold Cop.sem_shr, Cop.sem_shift; simpl.
      change Int64.iwordsize with (Int64.repr 64).
      change (Int64.ltu (Int64.repr 8) (Int64.repr 64)) with true; simpl.
      unfold Cop.sem_cmp; simpl.
      unfold Cop.sem_binarith; simpl.
      unfold Val.of_bool; simpl.
      unfold Vtrue, Vfalse.
      reflexivity.
    }

    unfold eval_inv, match_res, state.is_well_dst'.
    unfold bool_correct, Val.of_bool, BinrBPF.get_dst.
    unfold Int.cmpu.
    destruct negb; reflexivity.
    unfold Cop.sem_cast; simpl.
    destruct negb; reflexivity.
    intros.
    destruct negb; constructor; reflexivity.
  Qed.

End Is_well_dst.

Existing  Instance correct_function_is_well_dst.
