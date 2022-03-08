From bpf.comm Require Import State Monad.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check eval_ins_len.
eval_ins_len
     : M int
*)

Section Eval_ins_len.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (int:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_ins_len.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_ins_len.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => int32_correct x v.

  Instance correct_function3_eval_ins_len : forall a, correct_function3 p args res f fn nil false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    unfold stateM_correct in c.
    destruct c as (Hv_eq & Hst).
    subst.

    (** we need to get the value of pc in the memory *)
    destruct Hst. clear - p0 mins_len.
    destruct mins_len as (Hload_eq & Hge).

    eexists; exists m, Events.E0.

    split.
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
    split.
    {
      unfold match_res, State.eval_ins_len.
      split; reflexivity.
    }
    split.
    {
      constructor.
      reflexivity.
    }
    simpl.
    split; reflexivity.
  Qed.

End Eval_ins_len.

Existing  Instance correct_function3_eval_ins_len.
