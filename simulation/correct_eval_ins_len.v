From bpf.comm Require Import State Monad rBPFMonadOp.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

From bpf.simulation Require Import MatchState InterpreterRel.


Section Eval_ins_len.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (int:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M State.state res) := eval_ins_len.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_ins_len.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle) (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv State.state := fun x  => StateLess _ (int32_correct x).

  Instance correct_function_eval_ins_len : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    unfold eval_inv, is_state_handle in c.
    subst.

    (** we need to get the value of pc in the memory *)
    assert (MS':=MS).
    destruct MS. clear - MS' p0 mins_len.
    destruct mins_len as (Hload_eq & Hge).

    eexists; exists m, Events.E0.

    split_and; auto.
    {
      forward_star.
      unfold Coqlib.align; rewrite Ptrofs.add_zero_l.
      unfold Ptrofs.zero; simpl.
      unfold Mem.loadv in Hload_eq.
      apply Hload_eq.
      simpl.
      reflexivity.
      forward_star.
    }
    reflexivity.
    constructor. reflexivity.
    apply unmodifies_effect_refl.
  Qed.

End Eval_ins_len.

Existing  Instance correct_function_eval_ins_len.
