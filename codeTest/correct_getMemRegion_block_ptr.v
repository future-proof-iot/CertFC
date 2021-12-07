From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CommonLemma interpreter.

(**

static unsigned long long getMemRegion_block_ptr(struct memory_region *mr0)
{
  return 1LLU;
}

Definition getMemRegion_block_ptr (mr0: memory_region) : M val64_t := returnM (block_ptr mr0).

*)

Section GetMemRegion_block_ptr.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_region:Type)].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := getMemRegion_block_ptr.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_getMemRegion_block_ptr.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (match_region state_block)
       (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => True.

  Lemma correct_function3_eval_pc : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _mr0.

    unfold match_region in H1.
    destruct H1 as (o & Hptr & Hmatch).
    unfold match_region_at_ofs in Hmatch.
    destruct Hmatch as (_ & _ & (vptr & Hptr_load & Hinj)).
    subst v.

    (**according to the type of eval_pc:
         static unsigned long long getMemRegion_block_ptr(struct memory_region *mr0)
       1. return value should be  `Vlong (Int64.repr 1)`
       2. the memory is same
      *)
    exists (Vlong (Int64.repr 1)), m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_one; eauto.
      eapply step_return_1.
      +
        repeat econstructor; eauto.
      + Transparent Archi.ptr64.
        unfold Cop.sem_cast; simpl.
        reflexivity.
      + reflexivity.
    - simpl.
      constructor.
  Qed.

End GetMemRegion_block_ptr.
