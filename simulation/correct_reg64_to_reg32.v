From bpf.comm Require Import State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check reg64_to_reg32.
reg64_to_reg32
     : val64_t -> DxMonad.M valu32_t

*)

Section Reg64_to_reg32.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := reg64_to_reg32.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_reg64_to_reg32.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) args :=
    (dcons (fun x => StateLess (val64_correct x))
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x  => StateLess (val32_correct x).

  Instance correct_function_reg64_to_reg32 : forall a, correct_function p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _d.

    unfold eval_inv, val64_correct in c0.
    destruct c0 as (Hc_eq & (vl & Hvl_eq)).
    subst.

    (**according to the type of eval_pc:
         static unsigned long long get_addl(unsigned long long x, unsigned long long y)
       1. return value should be  x+y
       2. the memory is same
      *)
    eexists; exists m, Events.E0.

        split_and;auto;unfold step2.
    -
      repeat forward_star.
    - unfold eval_inv,match_res.
      simpl. unfold val32_correct.
      split ; eauto.
    - simpl.
      constructor.
      reflexivity.
    - apply unmodifies_effect_refl.
  Qed.

End Reg64_to_reg32.

Existing Instance correct_function_reg64_to_reg32.
