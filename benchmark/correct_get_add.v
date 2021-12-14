From bpf.src Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.benchmark Require Import clightlogicexample.

(**
unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}

get_add = 
fun x y : valu32_t => returnM (Val.add x y)
     : valu32_t -> valu32_t -> M valu32_t

*)

Section Get_add.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(valu32_t:Type); (valu32_t:Type)].
  Definition res : Type := (valu32_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_add.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_add.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless valu32_correct)
       (DList.DCons (stateless valu32_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => valu32_correct x v.

  Instance correct_function3_get_add : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _x.
    get_invariant_more _y.

    unfold stateless, valu32_correct in H1, H3.
    destruct H1 as (Hc_eq & (vi & Hvi_eq)).
    destruct H3 as (Hc0_eq & (vj & Hvj_eq)).
    subst c c0 v v0.

    (**according to the c function:
unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}
       1. return value should be  x+y
       2. the memory is same
      *)
    exists (Val.add (Vint vi) (Vint vj)), m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_one; eauto.
      eapply step_return_1.
      +
        repeat econstructor; eauto.
        Transparent Archi.ptr64.
        unfold Cop.sem_binary_operation.
        unfold Cop.sem_add, Cop.classify_add, Ctypes.typeconv; simpl.
        unfold Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast; simpl.
        reflexivity.
      + econstructor; eauto.
      + reflexivity.
    - simpl.
      exists (Int.add vi vj); reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Get_add.

Existing Instance correct_function3_get_add.
