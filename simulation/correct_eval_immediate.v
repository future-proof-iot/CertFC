From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check eval_immediate.
eval_immediate
     : int -> M val

 *)

Open Scope Z_scope.

Section Eval_immediate.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_immediate.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_immediate.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) args :=
    (dcons (fun x => StateLess (int32_correct x))
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x => StateLess (val64_correct x).

  Instance correct_function_eval_immediate : forall a, correct_function p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _ins.

    unfold eval_inv, int32_correct in c0.
    subst.

    eexists; exists m, Events.E0.

    split_and;auto.
    - repeat forward_star.
    -   unfold eval_inv, match_res, rBPFValues.sint32_to_vint, val64_correct.
        unfold Val.longofint; simpl.
        eauto.
    - constructor.
    - apply unmodifies_effect_refl.
  Qed.

End Eval_immediate.
Close Scope Z_scope.

Existing Instance correct_function_eval_immediate.
