From bpf.comm Require Import MemRegion State Monad.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

(**
static struct memory_region *eval_mrs_regions(struct bpf_state* st){
  return ( *st).mrs;
}

Print eval_mrs_regions.
eval_mrs_regions = 
fun st : stateM => Some (DxState.eval_mem_regions st, st)
     : M MyMemRegionsType

*)

Section Eval_mrs_regions.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [].
  Definition res : Type := (MyMemRegionsType:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_mrs_regions.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_mrs_regions.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess is_state_handle)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun re => StateFull (fun v st m => mrs_correct S re v st m).

  Instance correct_function_eval_mrs_regions : forall a, correct_function p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _st.

    unfold eval_inv, is_state_handle in c.
    subst v.

    assert (Hst' := MS).
    destruct Hst'. clear - MS p0 mem_regs.

    eexists. exists m, Events.E0.

    split_and.
    {
      repeat forward_star.

      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align, AST.Mptr; simpl.

      destruct mem_regs as (mem_regs & _).
      rewrite <- mem_regs.
      unfold AST.Mptr.
      simpl.
      reflexivity.
      reflexivity.
    }
    {
      unfold eval_inv, match_res, mrs_correct.
      unfold State.eval_mem_regions.
      split; [reflexivity |].
      destruct mem_regs as (_ & mem_regs).
      split;[ reflexivity | split; assumption].
    }
    constructor.
    auto.
    apply unmodifies_effect_refl.
  Qed.

End Eval_mrs_regions.

Existing Instance correct_function_eval_mrs_regions.
