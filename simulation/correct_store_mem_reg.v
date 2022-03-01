From bpf.comm Require Import State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clight Require Import interpreter.

From bpf.proof Require Import MatchState Clightlogic clight_exec CommonLemma CorrectRel.

(**
Check store_mem_reg.

store_mem_reg
     : memory_chunk -> val -> val -> M unit

 *)

Section Store_mem_reg.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_chunk:Type); val; val].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.store_mem_reg.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  Variable modifies : block. (* of the C code *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_store_mem_reg.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons (stateless match_chunk)
         (DList.DCons (val_ptr_correct state_block mrs_block ins_block)
            (DList.DCons (stateless val64_correct)
              (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef.

  Instance correct_function3_store_mem_reg : forall a, correct_function3 p args res f fn [modifies] false match_arg_list match_res a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, store_mem_reg, State.store_mem_reg, Mem.storev, INV, app.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  get_invariant _v.
  unfold stateM_correct in c2.
  unfold stateless, match_chunk in c3.
  unfold val_ptr_correct in c4.
  unfold stateless, val64_correct in c5.
  destruct c2 as (Hptr & Hmatch).
  destruct c4 as (Hc0_eq & b & ofs & Hvalid_blk & Hc0_ptr & Hneq_blk).
  destruct c5 as (Hc1_eq & vl & Hvl_eq).
  subst.

  unfold rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z in p1.
  unfold match_res.
(*
  assert (Hstore_eq: Mem.store c (bpf_m st) b (Ptrofs.unsigned ofs) (vlong_to_vint_or_vlong c (Vlong vl)) = Mem.store c m b (Ptrofs.unsigned ofs) (vlong_to_vint_or_vlong c (Vlong vl))). {
    eapply match_state_implies_store_equal; eauto.
  }
  rewrite Hstore_eq; clear Hstore_eq. *)
  unfold vlong_to_vint_or_vlong.
  destruct c; try constructor.
  all: destruct Mem.store eqn: Hstore; [| constructor].
  all: intros; exists Vundef; eexists; exists Events.E0.
  - (**r c = Mint8unsigned *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 1)) with 1%Z.
    simpl.
    unfold step2.
    forward_star.
    forward_star.
    forward_star.
    unfold Mem.storev.
    simpl.
    admit.
    forward_star.
    forward_star.
    forward_star.
    split.
    split; [ |reflexivity].
    admit.
    split; [constructor | ].
    admit.
  - (**r c = Mint16unsigned *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 2)) with 2%Z.
    simpl.
    unfold step2.
    forward_star.
    forward_star.
    forward_star.
    unfold Mem.storev.
    simpl.
    admit.
    forward_star.
    forward_star.
    forward_star.
    split.
    split; [ |reflexivity].
    admit.
    split; [constructor | ].
    admit.
  - (**r c = Mint32 *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 4)) with 4%Z.
    simpl.
    unfold step2.
    forward_star.
    forward_star.
    forward_star.
    unfold Mem.storev.
    simpl.
    admit.
    forward_star.
    forward_star.
    forward_star.
    split.
    split; [ |reflexivity].
    admit.
    split; [constructor | ].
    admit.
  - (**r c = Mint64 *)
    split.
    forward_star.
    change (Int.unsigned (Int.repr 8)) with 8%Z.
    simpl.
    unfold step2.
    forward_star.
    forward_star.
    forward_star.
    unfold Mem.storev.
    simpl.
    admit.
    forward_star.
    forward_star.
    forward_star.
    split.
    split; [ |reflexivity].
    admit.
    split; [constructor | ].
    admit.
    Unshelve.
    all: assumption.
Qed.

End Store_mem_reg.

Existing Instance correct_function3_store_mem_reg.
