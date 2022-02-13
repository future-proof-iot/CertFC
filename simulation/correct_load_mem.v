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

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

Definition val_ptr_correctM (blk: block) (x:val) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    x = v /\
    (exists ofs, v = Vptr blk ofs). (**r we should say the relation between memory_chunk and Vptr blk ofs: `valid_access_dec m chunk b ofs Readable` *)

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
                (DList.DCons (stateless match_chunk)
                             (DList.DCons (val_ptr_correctM mrs_block)
                                          (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => val64_correct x v /\ match_state state_block mrs_block ins_block st m.
Ltac exec_seq_of_labeled_statement :=
  match goal with
  | |- context[seq_of_labeled_statement ?X] =>
      let x := (eval simpl in (seq_of_labeled_statement X)) in
      change (seq_of_labeled_statement X) with x
  end.

  Instance correct_function3_load_mem : forall a, correct_function3 p args res f fn [] false match_arg_list match_res a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, INV.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  unfold stateM_correct in c1.
  unfold stateless, match_chunk in c2.
  unfold val_ptr_correctM in c3.
  destruct c1 as (Hptr & Hmatch).
  destruct c3 as (Hc0_eq & (ofs & Hv1_eq)).
(*
  destruct c3 as (Heq_c0 & (ofs & Heq_ptr) & (res0 & Hload0 & Hst0)  & (res1 & Hload1 & Hst1) & (res2 & Hload2 & Hst2) & (res3 & Hload3 & Hst3)). *)
  subst.

  (**according to:
       static unsigned long long load_mem(struct bpf_state* st, unsigned int chunk, unsigned long long v)
     1. return value should be Vlong.
     2. the memory is same
   *)
  
  destruct c.
  - exists (Vlong (Int64.repr 0)); subst; exists m, Events.E0.
    split.
    {
      eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                             econstructor; eauto|]].
      eapply Smallstep.star_refl.
      reflexivity.
    }
    split.
    { (**r match_res *)
      unfold match_res.
      split.
      unfold val64_correct.
      unfold State.load_mem.
      split.
      reflexivity.
      eexists; reflexivity.
      (**r match_state *)
      assumption.
    }
    split.
    constructor.
    simpl; auto.
  - (**r destruct Hmatch. *)
    eexists. exists m, Events.E0.
    split.
    {
      forward_star.
      unfold rBPFAST.well_chunk_Z.
      fold Int.one; rewrite Int.unsigned_one.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      admit.
      (**r match_state should say the load/store permission of mrs_block? *)
      apply Hload0.
      simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      repeat forward_star.
      reflexivity.
    }
    split.
    unfold State.load_mem.
    unfold _to_vlong, Regs.val64_zero.
    unfold match_res, val64_correct.
    split; [| assumption].
    rewrite Hst0.
    split; [reflexivity |].
    eexists; reflexivity.

    split.
    simpl.
    constructor.
    simpl.
    split; reflexivity.
  - exists (Vlong (Int64.repr 0)); subst; exists m, Events.E0.
    split.
    {
      eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                             econstructor; eauto|]].
      eapply Smallstep.star_refl.
      reflexivity.
    }
    split.
    { (**r match_res *)
      unfold match_res.
      split.
      unfold val64_correct.
      unfold State.load_mem.
      split.
      reflexivity.
      eexists; reflexivity.
      (**r match_state *)
      assumption.
    }
    split.
    constructor.
    simpl; auto.
  -
    eexists. exists m, Events.E0.
    split.
    {
      forward_star.
      repeat forward_star.
      unfold rBPFAST.well_chunk_Z.
      rewrite Int_unsigned_repr_n with (n:=2%Z); [| try lia].
      simpl.
      forward_star.
      repeat forward_star.
      forward_star.
      repeat forward_star.
      apply Hload1.
      simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      repeat forward_star.
      reflexivity.
    }
    split.
    unfold State.load_mem.
    unfold _to_vlong, Regs.val64_zero.
    unfold match_res, val64_correct.
    split; [| assumption].
    rewrite Hst1.
    split; [reflexivity |].
    eexists; reflexivity.

    split.
    simpl.
    constructor.
    simpl.
    split; reflexivity.
  -
    eexists. exists m, Events.E0.
    split.
    {
      forward_star.
      repeat forward_star.
      unfold rBPFAST.well_chunk_Z.
      rewrite Int_unsigned_repr_n with (n:=4%Z); [| try lia].
      simpl.
      forward_star.
      repeat forward_star.
      forward_star.
      repeat forward_star.
      apply Hload2.
      simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      repeat forward_star.
      reflexivity.
    }
    split.
    unfold State.load_mem.
    unfold _to_vlong, Regs.val64_zero.
    unfold match_res, val64_correct.
    split; [| assumption].
    rewrite Hst2.
    split; [reflexivity |].
    eexists; reflexivity.

    split.
    simpl.
    constructor.
    simpl.
    split; reflexivity.
  -
    eexists. exists m, Events.E0.
    split.
    {
      forward_star.
      repeat forward_star.
      unfold rBPFAST.well_chunk_Z.
      rewrite Int_unsigned_repr_n with (n:=8%Z); [| try lia].
      simpl.
      forward_star.
      repeat forward_star.
      forward_star.
      repeat forward_star.
      apply Hload3.
      simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
      repeat forward_star.
      reflexivity.
    }
    split.
    unfold State.load_mem.
    unfold _to_vlong, Regs.val64_zero.
    unfold match_res, val64_correct.
    split; [| assumption].
    rewrite Hst3.
    split; [reflexivity |].
    eexists; reflexivity.

    split.
    simpl.
    constructor.
    simpl.
    split; reflexivity.
  - exists (Vlong (Int64.repr 0)); subst; exists m, Events.E0.
    split.
    {
      eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                             econstructor; eauto|]].
      eapply Smallstep.star_refl.
      reflexivity.
    }
    split.
    { (**r match_res *)
      unfold match_res.
      split.
      unfold val64_correct.
      unfold State.load_mem.
      split.
      reflexivity.
      eexists; reflexivity.
      (**r match_state *)
      assumption.
    }
    split.
    constructor.
    simpl; auto.
  - exists (Vlong (Int64.repr 0)); subst; exists m, Events.E0.
    split.
    {
      eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                             econstructor; eauto|]].
      eapply Smallstep.star_refl.
      reflexivity.
    }
    split.
    { (**r match_res *)
      unfold match_res.
      split.
      unfold val64_correct.
      unfold State.load_mem.
      split.
      reflexivity.
      eexists; reflexivity.
      (**r match_state *)
      assumption.
    }
    split.
    constructor.
    simpl; auto.
  - exists (Vlong (Int64.repr 0)); subst; exists m, Events.E0.
    split.
    {
      eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                             econstructor; eauto|]].
      eapply Smallstep.star_refl.
      reflexivity.
    }
    split.
    { (**r match_res *)
      unfold match_res.
      split.
      unfold val64_correct.
      unfold State.load_mem.
      split.
      reflexivity.
      eexists; reflexivity.
      (**r match_state *)
      assumption.
    }
    split.
    constructor.
    simpl; auto.
  - exists (Vlong (Int64.repr 0)); subst; exists m, Events.E0.
    split.
    {
      eapply Smallstep.star_step; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor.
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                             econstructor; eauto|]].
      eapply Smallstep.star_refl.
      reflexivity.
    }
    split.
    { (**r match_res *)
      unfold match_res.
      split.
      unfold val64_correct.
      unfold State.load_mem.
      split.
      reflexivity.
      eexists; reflexivity.
      (**r match_state *)
      assumption.
    }
    split.
    constructor.
    simpl; auto.
Qed.

End Load_mem.

Existing Instance correct_function3_load_mem.
