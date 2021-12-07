From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CommonLemma interpreter.

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

static unsigned long long getMemRegion_block_size(struct memory_region *mr2)
{
  return ( *mr2).block_size;
}

Definition getMemRegion_block_size (mr2: memory_region): M val64_t := returnM (block_size mr2).

*)

Section GetMemRegion_block_size.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_region:Type)].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := getMemRegion_block_size.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_getMemRegion_block_size.

Definition my_match_region (bl_region : block) (mr: memory_region) (v: val64_t) (st: stateM) (m:Memory.Mem.mem) :=
  exists o, v = Vptr bl_region o /\
              match_region_at_ofs mr bl_region o m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (my_match_region state_block)
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
    get_invariant_more _mr2.

    unfold my_match_region in H1.
    destruct H1 as (o & Hptr & Hmatch).
    unfold match_region_at_ofs in Hmatch.
    destruct Hmatch as (_ & (vsize & Hsize_load & Hinj) & _).
    subst v.

    (**according to the type:
         static unsigned long long getMemRegion_start_addr(struct memory_region *mr1)
       1. return value should be  `Vlong vaddr`
       2. the memory is same
      *)
    exists (Vlong vsize), m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_one; eauto.
      eapply step_return_1.
      +
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        eapply deref_loc_copy. (**r TODO: always deref_loc_copy? could we do something? *)
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity. (*Compute (Ctypes.access_mode (typeof
     (Efield
        (Ederef
           (Etempvar _mr1
              (Clightdefs.tptr (Ctypes.Tstruct _memory_region Ctypes.noattr)))
           (Ctypes.Tstruct _memory_region Ctypes.noattr)) _start_addr
        Clightdefs.tulong))).*)
        eapply deref_loc_value. (**r TODO: here is deref_loc_value, could we do something? *)
        reflexivity.
        unfold Coqlib.align.
        simpl.
        fold Ptrofs.zero.
        unfold Mem.loadv in Hsize_load.
        rewrite <- Hsize_load; reflexivity.
      + Transparent Archi.ptr64.
        unfold Cop.sem_cast; simpl.
        reflexivity.
      + reflexivity.
    - simpl.
      constructor.
  Qed.

End GetMemRegion_block_size.
