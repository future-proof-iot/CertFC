From bpf.src Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.benchmark Require Import clightlogicexample.

(**
static struct memory_region *eval_mem_regions(struct bpf_state* st){
  return ( *st).mrs;
}

Print eval_mem_regions.
eval_mem_regions = 
fun st : stateM => Some (DxState.eval_mem_regions st, st)
     : M MyMemRegionsType

*)

Section Eval_mem_regions.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [].
  Definition res : Type := (MyMemRegionsType:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_mem_regions.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_mem_regions.

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons stateM_correct
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun _ _ _ _ => True.

  Instance correct_function3_eval_mem_regions : correct_function3 p args res f fn (nil) false match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant_more _st.

    unfold stateM_correct in H1.
    destruct H1 as (Hv_eq & Hst).
    destruct Hst.
    clear minj mpc mflags mregs mperm.
    destruct mrs_num as (Hmrs_num_ld & Hmrs_num_gt).
    destruct mem_regs as (mem_regs & Hmem_regions_length).
    subst v.

    destruct (bpf_mrs st).
    {
      simpl in Hmem_regions_length.
      rewrite <- Hmem_regions_length in Hmrs_num_gt.
      simpl in Hmrs_num_gt.
      lia.
    }
    destruct mem_regs as (Hmem_regs & _).
    unfold match_region_at_ofs in Hmem_regs.
    destruct Hmem_regs as ((vl & Hstart_addr & _) & _).
    unfold Mem.loadv, size_of_regs in Hstart_addr.
    simpl in Hstart_addr.

    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      apply Smallstep.plus_star.
      repeat forward_clight.

      Transparent Archi.ptr64.
      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align, AST.Mptr; simpl.

      rewrite Hstart_addr; reflexivity.

      reflexivity.
      reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Eval_mem_regions.

Existing Instance correct_function3_eval_mem_regions.
