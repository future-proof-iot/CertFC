From bpf.src Require Import DxIntegers DxValues DxList64 DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.benchmark Require Import clightlogicexample.

(**
unsigned long long list_get(unsigned long long *l, int idx)
{
  return *(l + idx);
}

Print list_get.
list_get = 
fun (l : DxList64.MyListType) (idx : sint32_t) =>
returnM (DxList64.MyListIndexs32 l idx)
     : DxList64.MyListType -> sint32_t -> M int64_t
*)

Section List_get.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(MyListType:Type); (sint32_t:Type)].
  Definition res : Type := (int64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := list_get.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_list_get.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless MyListType_correct)
        (DList.DCons (stateless sint32_correct)
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => int64_correct x v.

  Instance correct_function3_list_get : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _ins.

    unfold stateless, int64_correct in H1.
    subst v.

    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      repeat forward_clight.

      reflexivity.
      reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End List_get.

Existing Instance correct_function3_list_get.
