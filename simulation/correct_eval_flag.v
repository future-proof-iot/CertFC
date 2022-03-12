From bpf.comm Require Import Flag State Monad.

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.



Section Eval_flag.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (bpf_flag:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.eval_flag.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_flag.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    dcons (fun x => StateLess (is_state_handle)) (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x => StateLess (flag_correct x).

  Instance correct_function_eval_flag : forall a, correct_function p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    unfold eval_inv, is_state_handle in c.
    subst.

    (** we need to get the value of pc in the memory *)
    destruct MS.
    unfold Mem.loadv in mflags.
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static int eval_flag(struct bpf_state* st)
       1. return value should be Vint
       2. the memory is same
      *)
    exists (Vint (int_of_flag (flag st))), m, Events.E0.

    split_and; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.

      unfold Coqlib.align; simpl.
      rewrite Ptrofs.add_zero_l.
      rewrite mflags; reflexivity.
      econstructor; eauto.
    - simpl.
      constructor.
    - constructor.
      reflexivity.
    - constructor ;auto.
    - apply unmodifies_effect_refl.
  Qed.

End Eval_flag.

Existing  Instance correct_function_eval_flag.
