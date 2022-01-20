From bpf.comm Require Import State Monad.
From bpf.src Require Import DxValues DxInstructions.
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
  Definition args : list Type := [(memory_chunk:Type); valptr8_t].
  Definition res : Type := (val64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.load_mem.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_load_mem.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
                (DList.DCons (stateless match_chunk)
                             (DList.DCons (stateless val_ptr_correct)
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
  get_invariant_more _st.
  get_invariant_more _chunk.
  get_invariant_more _addr.
  unfold stateM_correct in H0.
  unfold stateless, match_chunk in H2.
  unfold stateless, val_ptr_correct in H4.
  destruct H0 as (Hptr & Hmatch).
  destruct H4 as (Hc0_eq & (b & ofs & Hptr_eq)).
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
      split; unfold val64_zero.
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
      repeat forward_star.
      unfold rBPFAST.well_chunk_Z.
      fold Int.one; rewrite Int.unsigned_one.
      simpl.
      forward_star.
      repeat forward_star.
      forward_star.
      repeat forward_star. (**r we lose something in the precondition! *)
      admit.
      eapply Mem.load_unchanged_on.
      apply munchange.
      intros.
      simpl.

      admit.
      forward_star.
      repeat forward_star.

    }
















      
      forward_plus.
      eapply Smallstep.plus_one; eauto.
      repeat (econstructor; eauto; try (deref_loc_tactic)).

      Transparent Archi.ptr64.

      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align; simpl.
      unfold Mem.loadv in Hreg_load.
      assert (Heq: Ptrofs.repr (8 * id_of_reg c) = Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (Int.repr (id_of_reg c)))). {
        unfold Ptrofs.mul, Ptrofs.of_intu.
        unfold Ptrofs.of_int.
        repeat rewrite Ptrofs.unsigned_repr.
        rewrite Int.unsigned_repr.
        reflexivity.
        rewrite Int_max_unsigned_eq64.
        unfold id_of_reg; destruct c; lia.
        rewrite Ptrofs_max_unsigned_eq64.
        rewrite Int.unsigned_repr.
        unfold id_of_reg; destruct c; lia.
        rewrite Int_max_unsigned_eq64.
        unfold id_of_reg; destruct c; lia.
        rewrite Ptrofs_max_unsigned_eq64.
        lia.
      }
      rewrite Heq in Hreg_load.
      rewrite Hreg_load.
      reflexivity.

      unfold Cop.sem_cast; reflexivity.
    -
      unfold match_res.
      unfold val64_correct.
      unfold DxState.eval_reg.
      symmetry; assumption.
    - unfold DxState.eval_reg; exists vl; symmetry; assumption.
    -
      simpl.
      constructor.
  Qed.
  

End Load_mem.

Existing Instance correct_function3_load_mem.
