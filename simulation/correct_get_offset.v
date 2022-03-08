From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check get_offset.
get_offset
     : int64 -> M int

 *)

Open Scope Z_scope.

Section Get_offset.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (int:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_offset.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_offset.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless int64_correct)
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => int32_correct x v.

  Instance correct_function3_get_offset : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _ins.

    unfold stateless, int64_correct in c0.
    subst.

    eexists; exists m, Events.E0.

    split.
    {
      repeat forward_star.
    }
    split.
    {
      unfold match_res, int32_correct, Regs.get_offset; simpl.
      (**r according to the clight representation, we delete the self-defined library int16 in order to simplify the proof here *)
      reflexivity.
    }
    split;[constructor; reflexivity | split; reflexivity].
  Qed.

End Get_offset.
Close Scope Z_scope.

Existing Instance correct_function3_get_offset.
