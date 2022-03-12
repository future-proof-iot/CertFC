From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Memory Clight.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

(**
int get_immediate(unsigned long long ins)
{
  return (int) (ins >> 32LLU);
}

Print get_immediate.
get_immediate = 
fun ins : int64_t => returnM (int64_to_sint32 (Int64.shru ins int64_32))
     : int64_t -> M sint32_t
*)

Section Get_immediate.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (int:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_immediate.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_immediate.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) args :=
    (dcons (fun x => StateLess (int64_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x => StateLess (int32_correct x).

  Instance correct_function_get_immediate : forall a, correct_function p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _ins.

    unfold eval_inv, int64_correct in c0.
    subst v.

    eexists. exists m, Events.E0.

    split_and; unfold step2;auto.
    - repeat forward_star.
    - simpl.
      constructor.
    - constructor.
      reflexivity.
    - apply unmodifies_effect_refl.
  Qed.

End Get_immediate.

Existing Instance correct_function_get_immediate.
