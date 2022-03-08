From bpf.comm Require Import State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.


(**
Check load_mem.

load_mem
     : memory_chunk -> valu32_t -> M val64_t

 *)

Section Load_mem.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_chunk:Type); val].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.load_mem.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_load_mem.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (stateless match_chunk)
         (DList.DCons (val_ptr_correct state_block mrs_block ins_block)
            (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v /\ match_state state_block mrs_block ins_block st m.

  Instance correct_function3_load_mem : forall a, correct_function3 p args res f fn [] false match_arg_list match_res a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, load_mem, State.load_mem, Mem.loadv, INV, app, _to_vlong.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  unfold stateM_correct in c1.
  unfold stateless, match_chunk in c2.
  unfold val_ptr_correct in c3.
  destruct c1 as (Hptr & Hmatch).
  destruct c3 as (c3 & _).
  subst.

  unfold rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z in p1.
  unfold match_res, val64_correct.

  assert (Hload_implies: forall v,
    Mem.loadv c (bpf_m st) v1 =  Some v -> Mem.loadv c m v1 = Some v). {
    unfold Mem.loadv.
    intros.
    destruct v1; try inversion H0.
    rewrite H2.
    eapply match_state_implies_loadv_equal; eauto.
  }
  destruct c, v1; try constructor.
  - (**r c = Mint8unsigned *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    all: rewrite <- Hv_eq in *; destruct Val.eq; [constructor|].
    all: intros; eexists; exists m, Events.E0.
    + (**r v = Vint i0 *)
      split.
      forward_star.
      change (Int.unsigned (Int.repr 1)) with 1%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
      split; [split; [split; [reflexivity |] | assumption] |].
      eexists; reflexivity.
      split; [constructor | split; reflexivity].
    + (**r v = Vlong i0: it should be impossible *)
      apply Mem.load_type in Hload.
      rewrite Hv_eq in Hload.
      inversion Hload.
  - (**r c = Mint16unsigned *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    all: rewrite <- Hv_eq in *; destruct Val.eq; [constructor|].
    all: intros; eexists; exists m, Events.E0.
    + split.
      forward_star.
      change (Int.unsigned (Int.repr 2)) with 2%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
      split; [split; [split; [reflexivity |] | assumption] |].
      eexists; reflexivity.
      split; [constructor | split; reflexivity].
    + apply Mem.load_type in Hload.
      rewrite Hv_eq in Hload.
      inversion Hload.
  - (**r c = Mint32 *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    all: rewrite <- Hv_eq in *; destruct Val.eq; [constructor|].
    all: intros; eexists; exists m, Events.E0.
    + split.
      forward_star.
      change (Int.unsigned (Int.repr 4)) with 4%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
      split; [split; [split; [reflexivity |] | assumption] |].
      eexists; reflexivity.
      split; [constructor | split; reflexivity].
    + apply Mem.load_type in Hload.
      rewrite Hv_eq in Hload.
      inversion Hload.
  - (**r c = Mint64 *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq.
    all: rewrite <- Hv_eq in *; destruct Val.eq eqn: Heq; [constructor|].
    all: try (apply Mem.load_type in Hload as Hload1; rewrite Hv_eq in Hload1; inversion Hload1).
    all: intros; eexists; exists m, Events.E0.
    + intuition congruence.
    + split.
      forward_star.
      change (Int.unsigned (Int.repr 8)) with 8%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      rewrite Hv_eq; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      simpl.
      forward_star.
      rewrite Hv_eq.
      split; [split; [split; [reflexivity |] | assumption] |].
      eexists; reflexivity.
      split; [constructor | split; reflexivity].
      Unshelve.
      all: assumption.
Qed.

End Load_mem.

Existing Instance correct_function3_load_mem.
