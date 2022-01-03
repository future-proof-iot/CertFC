From bpf.src Require Import DxIntegers DxValues DxList64 DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

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

  Variable ins_block: block.
  Variable ins_block_length: nat.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_list_get.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (MyListType_correct ins_block ins_block_length)
        (DList.DCons (stateless (pc_correct ins_block_length)) (**r here we need to say the constraints with the input list *)
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => int64_correct x v.

  Instance correct_function3_list_get : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    unfold list_get.
    simpl.
    unfold MyListIndexs32, MyList.index_s32.
    repeat intro.
    get_invariant_more _l.
    get_invariant_more _idx.

    unfold MyListType_correct in H1.
    destruct H1 as (Hv_eq & H1).
    unfold stateless, pc_correct in H3.
    destruct H3 as (Hv0_eq & Hrange & Hrange_max).
    specialize H1 with (Z.to_nat (Int.signed c0)).
    assert (Hc0_eq: Z.of_nat (Z.to_nat (Int.signed c0)) = Int.signed c0). {
      apply Z2Nat.id.
      lia.
    }
    rewrite Hc0_eq in H1; clear Hc0_eq.
    apply H1 in Hrange as Hrange1.
    destruct Hrange1 as (vl & Hnth & Hload).
    subst v v0.

    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.

      rewrite Ptrofs.add_zero_l; simpl.
      unfold Ptrofs.of_ints, Ptrofs.mul.
      unfold Mem.loadv in Hload.
      repeat rewrite Ptrofs.unsigned_repr.
      rewrite Ptrofs.unsigned_repr in Hload.
      rewrite Hload; reflexivity.
      lia.
      lia.
      rewrite Ptrofs_max_unsigned_eq32.
      lia.
      lia.
      lia.
      rewrite Ptrofs_max_unsigned_eq32.
      lia.

      Transparent Archi.ptr64.
      simpl.
      unfold Cop.sem_cast; simpl.
      apply nth_error_nth with (d:= Int64.zero) in Hnth.
      rewrite <- Hnth.
      reflexivity.

    - simpl.
      constructor.
  Qed.

End List_get.

Existing Instance correct_function3_list_get.

