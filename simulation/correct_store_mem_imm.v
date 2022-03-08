From bpf.comm Require Import State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

(**

Check store_mem_imm.
store_mem_imm
     : val -> memory_chunk -> val -> M unit

 *)

Section Store_mem_imm.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [val; (memory_chunk:Type); val].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.store_mem_imm.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Variable modifies : block. (* of the C code *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_store_mem_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (val_ptr_correct state_block mrs_block ins_block)
         (DList.DCons (stateless match_chunk)
            (DList.DCons (stateless val32_correct)
              (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef.

  Instance correct_function3_store_mem_imm : forall ptr ck v, correct_function3 p args res f fn [(modified_block ptr ins_block)] false match_arg_list match_res (DList.DCons ptr
      (DList.DCons ck
         (DList.DCons v
              (DList.DNil _)))).
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, store_mem_imm, State.store_mem_imm, Mem.storev, INV, app.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  get_invariant _v.
  unfold stateM_correct in c.
  unfold stateless, match_chunk in c0.
  unfold val_ptr_correct in c1.
  unfold stateless, val32_correct in c2.
  destruct c as (Hptr & Hmatch).
  destruct c1 as (Hc0_eq & Hst).
  destruct c2 as (Hc1_eq & vi & Hvi_eq).
  subst.

  unfold rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z in p1.
  unfold match_res.
  unfold vint_to_vint_or_vlong.
  destruct ck; try constructor.
  all: destruct v2; try constructor.
  all: destruct Mem.store eqn: Hstore; [| constructor].
  all: eapply store_reg_preserive_match_state in Hmatch as Hstore_m2; eauto.
  all: destruct Hstore_m2 as (m2 & Hstore_m2 & Hmatch_m2).
  all: intros; exists Vundef, m2, Events.E0.
  - (**r c = Mint8unsigned *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 1)) with 1%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    split.
    split; [ assumption |reflexivity].
    split; [constructor | ].
    unfold modified_block.
    unfold unmodifies_effect.
    eapply Mem.store_unchanged_on; eauto.
    intros.
    intro.
    apply H1.
    unfold In.
    left; reflexivity.
  - (**r c = Mint16unsigned *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 2)) with 2%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    split.
    split; [ assumption |reflexivity].
    split; [constructor | ].
    unfold modified_block.
    unfold unmodifies_effect.
    eapply Mem.store_unchanged_on; eauto.
    intros.
    intro.
    apply H1.
    unfold In.
    left; reflexivity.
  - (**r c = Mint32 *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 4)) with 4%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    split.
    split; [ assumption |reflexivity].
    split; [constructor | ].
    unfold modified_block.
    unfold unmodifies_effect.
    eapply Mem.store_unchanged_on; eauto.
    intros.
    intro.
    apply H1.
    unfold In.
    left; reflexivity.
  - (**r c = Mint64 *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 8)) with 8%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    simpl.
    split.
    split; [ assumption |reflexivity].
    split; [constructor | ].
    unfold modified_block.
    unfold unmodifies_effect.
    eapply Mem.store_unchanged_on; eauto.
Qed.

End Store_mem_imm.

Existing Instance correct_function3_store_mem_imm.
