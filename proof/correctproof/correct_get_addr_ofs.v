From bpf.comm Require Import State Monad.
From bpf.src Require Import DxIntegers DxValues DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
unsigned int get_addr_ofs(unsigned long long x, int ofs)
{
  return (unsigned int) (x + (unsigned long long) ofs);
}

Print get_addr_ofs.
get_addr_ofs = 
fun (x : val64_t) (ofs : sint32_t) =>
returnM (val_intuoflongu (Val.addl x (Val.longofintu (sint32_to_vint ofs))))
     : val64_t -> sint32_t -> M valu32_t

*)

Section Get_addr_ofs.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val64_t:Type); (sint32_t:Type)].
  Definition res : Type := (valu32_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_addr_ofs.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_addr_ofs.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless val64_correct)
       (DList.DCons (stateless sint32_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => valu32_correct x v.

  Instance correct_function3_get_addr_ofs : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _x.
    get_invariant_more _ofs.

    unfold stateless, val64_correct in H0.
    unfold stateless, sint32_correct in H2.
    destruct H0 as (Hc_eq & (vi & Hvi_eq)).
    subst c v v0.

    (**according to the type of eval_pc:
unsigned int get_addr_ofs(unsigned long long x, int ofs)
{
  return (unsigned int) (x + (unsigned long long) ofs);
}
       1. return value should be  x+y
       2. the memory is same
      *)
    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.
    - simpl.
      eexists; reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Get_addr_ofs.

Existing Instance correct_function3_get_addr_ofs.
