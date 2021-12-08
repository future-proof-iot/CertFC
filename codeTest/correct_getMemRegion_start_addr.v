From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma interpreter.

(**

struct memory_region {
  unsigned long long start_addr;
  unsigned long long block_size;
  unsigned long long block_ptr;
};

struct memory_regions {
  struct memory_region* bpf_ctx;
  struct memory_region* bpf_stk;
  struct memory_region* content;
};

static unsigned long long getMemRegion_start_addr(struct memory_region *mr1)
{
  return ( *mr1).start_addr;
}

Definition getMemRegion_start_addr (mr1: memory_region): M val64_t := returnM (start_addr mr1).

static unsigned long long getMemRegion_block_size(struct memory_region *mr2)
{
  return ( *mr2).block_size;
}

Definition getMemRegion_block_size (mr2: memory_region): M val64_t := returnM (block_size mr2).

*)

Section GetMemRegion_start_addr.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_region:Type)].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := getMemRegion_start_addr.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_getMemRegion_start_addr.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (my_match_region state_block)
       (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v.

  Instance correct_function3_getMemRegion_start_addr : correct_function3 p args res f fn (nil) true match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _mr1.

    unfold my_match_region in H1.
    destruct H1 as (o & Hptr & Hmatch).
    unfold match_region_at_ofs in Hmatch.
    destruct Hmatch as ((vaddr & Haddr_load & Hinj) & _ & _).
    subst v.

    (**according to the type:
         static unsigned long long getMemRegion_start_addr(struct memory_region *mr1)
       1. return value should be  `Vlong vaddr`
       2. the memory is same
      *)
    exists (Vlong vaddr), m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_one; eauto.
      eapply step_return_1.
      +
        repeat (econstructor; eauto; try deref_loc_tactic).
        unfold Coqlib.align.
        simpl.
        fold Ptrofs.zero.
        rewrite Ptrofs.add_zero.
        unfold Mem.loadv in Haddr_load.
        rewrite <- Haddr_load; reflexivity.
      + Transparent Archi.ptr64.
        unfold Cop.sem_cast; simpl.
        reflexivity.
      + reflexivity.
    - assumption.
    - exists vaddr; assumption.
    - simpl.
      constructor.
  Qed.

End GetMemRegion_start_addr.

Existing Instance correct_function3_getMemRegion_start_addr.
