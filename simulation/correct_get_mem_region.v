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

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
      (DList.DCons pc_correct
        (DList.DCons (match_region_list mrs_block)
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun r v st m => match_region mrs_block r v st m.

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
    repeat intro.
    get_invariant _n.
    get_invariant _mrs.

    unfold pc_correct in c1.
    destruct c1 as (Hv_eq & Hrange & Hmax).
    unfold match_region_list in c2.
    destruct c2 as (Hv0_eq & Hmrs_eq & Hmrs_num_eq & Hmatch).
    subst.

    eexists; exists m, Events.E0.
    split.
    {
      repeat forward_star.
    }
    split.
    {
      unfold match_res, match_res, MyMemRegionsIndexnat, Memory_regions.index_nat.
      unfold match_region.
      rewrite Ptrofs.add_zero_l.
      eexists.
      split; [reflexivity |].
      simpl.
      unfold Ctypes.align_attr; simpl.
      unfold Z.max; simpl.
      unfold align; simpl.
      (**r because 0<=c < length mrs, so we know nth_error must return Some mr *)
      rewrite <- Hmrs_num_eq in Hrange.
      apply memory_region_in_nth_error with (n:=c) (l:= bpf_mrs st) in Hrange as Hnth_error.
      destruct Hnth_error as (mr & Hnth_error).
      rewrite Hnth_error.
      unfold Ptrofs.of_intu, Ptrofs.of_int.
      unfold Ptrofs.mul.
      rewrite Ptrofs.unsigned_repr; [| change Ptrofs.max_unsigned with 4294967295%Z; lia].
      rewrite Ptrofs.unsigned_repr; [| rewrite Int.unsigned_repr; [lia | change Int.max_unsigned with Ptrofs.max_unsigned; lia]].
      rewrite Int.unsigned_repr; [ | change Int.max_unsigned with Ptrofs.max_unsigned; lia].
      unfold match_list_region in Hmatch.
      assert (Hlen: (0 <= c < Datatypes.length (bpf_mrs st))%nat). {
        lia.
      }
      specialize (Hmatch c Hlen).
      apply nth_error_nth with (d:= default_memory_region) in Hnth_error.
      rewrite Hnth_error in Hmatch.
      assumption.
    }
    split.
    constructor.
    simpl; split; reflexivity.
Qed.

End Get_mem_region.

Existing Instance correct_function3_get_mem_region.

