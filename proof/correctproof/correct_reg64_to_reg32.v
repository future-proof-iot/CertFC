From bpf.comm Require Import State Monad.
From bpf.src Require Import DxValues DxInstructions.
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

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val64_t:Type)].
  Definition res : Type := (valu32_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := reg64_to_reg32.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_reg64_to_reg32.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless val64_correct)
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => valu32_correct x v.

  Instance correct_function3_reg64_to_reg32 : forall a, correct_function3 p args res f fn nil true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _d.

    unfold stateless, val64_correct in H0.
    completer.
    subst.

    (**according to the type of eval_pc:
         static unsigned long long get_addl(unsigned long long x, unsigned long long y)
       1. return value should be  x+y
       2. the memory is same
      *)
    eexists; exists m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.
    - simpl.
      eexists; reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Reg64_to_reg32.

Existing Instance correct_function3_reg64_to_reg32.
