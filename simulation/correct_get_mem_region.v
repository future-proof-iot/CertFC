From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs State Monad rBPFAST rBPFValues.
From bpf.monadicmodel Require Import rBPFInterpreter.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

(*
Check get_mem_region.

get_mem_region
     : nat -> MyMemRegionsType -> M memory_region *)

Section Get_mem_region.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [(nat:Type); (list memory_region:Type)].
  Definition res : Type := (memory_region:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_mem_region.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_mem_region.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
      (DList.DCons (stateless nat_correct)
        (DList.DCons (mrs_correct state_block mrs_block ins_block)
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun r v st m => mr_correct state_block mrs_block ins_block r v st m.

Lemma memory_region_in_nth_error:
  forall n l
    (Hrange : (0 <= Z.of_nat n < Z.of_nat (List.length l))%Z),
      exists (m:memory_region), nth_error l n = Some m.
Proof.
  intros.
  destruct Hrange as (Hlow & Hhigh).
  rewrite <- Nat2Z.inj_lt in Hhigh.
  rewrite <- List.nth_error_Some in Hhigh.
  destruct (nth_error l n).
  - exists m; reflexivity.
  - exfalso; apply Hhigh; reflexivity.
Qed.


  Instance correct_function3_get_mem_region : forall a, correct_function3 p args res f fn (nil) true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    unfold INV.
    unfold f.
    repeat intro; simpl.
    destruct get_mem_region eqn: Hregion; [|constructor].
    destruct p0.
    intros.
    get_invariant _n.
    get_invariant _mrs.

    unfold stateless, nat_correct in c1.
    unfold mrs_correct, match_regions in c2.
    destruct c2 as (Hv0_eq & Hmrs_eq & (Hmrs_num_eq & Hrange & Hmatch) & Hst).
    subst.

    eexists; exists m, Events.E0.
    split.
    {
      unfold step2.
      repeat forward_star.
    }

    unfold get_mem_region in Hregion.
    context_destruct_if_inversion.
    rewrite Nat.ltb_lt in Hcond.
    unfold match_list_region in Hmatch.
    rewrite Hmrs_num_eq in Hmatch.
    assert (HrangeNat: (0 <= c < mrs_num st)%nat) by lia.
    specialize (Hmatch c HrangeNat).
    (**r because 0<=c < length mrs, so we know nth_error must return Some mr *)
    assert (HrangeZ: (0 <= Z.of_nat c < Z.of_nat (mrs_num st))%Z) by lia.
    rewrite <- Hmrs_num_eq in HrangeZ.
    apply memory_region_in_nth_error with (n:=c) (l:= bpf_mrs st) in HrangeZ as Hnth_error.
    destruct Hnth_error as (mr & Hnth_error).
    rewrite Hnth_error in H1.
    inversion H1.
    eapply nth_error_nth in Hnth_error.
    rewrite Hnth_error in Hmatch.
    subst mr.
    subst s.
    split.
    {
      unfold match_res, mr_correct, match_region.
      split.
      rewrite <- Hnth_error.
      apply nth_In; lia.
      split; [| assumption].
      rewrite Ptrofs.add_zero_l.
      eexists.
      split; [reflexivity |].
      simpl.
      unfold Ctypes.align_attr; simpl.
      unfold Z.max, align; simpl.
      unfold Ptrofs.of_intu, Ptrofs.of_int.
      unfold Ptrofs.mul.
      change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16%Z.
      rewrite Hmrs_num_eq in Hrange.
      change Ptrofs.max_unsigned with Int.max_unsigned in Hrange.
      assert (HrangeZ_of_Nat: (0 <= Z.of_nat c < Int.max_unsigned)%Z) by lia.
      rewrite Int.unsigned_repr; [| lia].
      change Int.max_unsigned with Ptrofs.max_unsigned in HrangeZ_of_Nat.
      rewrite Ptrofs.unsigned_repr; [| lia].
      assumption.
    }
    split.
    constructor.

    split; reflexivity.
Qed.

End Get_mem_region.

Existing Instance correct_function3_get_mem_region.

