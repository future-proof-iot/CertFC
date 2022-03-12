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
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [val; (memory_chunk:Type); val].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.store_mem_reg.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_store_mem_reg.


  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    dcons (fun x => StateLess is_state_handle)
      (dcons (fun x => StateLess (eq x))
         (dcons (fun x => StateLess (match_chunk x))
            (dcons (fun x => StateLess (val64_correct x))
              (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x => StateLess (eq Vundef).


  Instance correct_function_store_mem_reg : forall ck ptr v, correct_function p args res f fn ModSomething false match_state match_arg_list match_res (DList.DCons ptr
      (DList.DCons ck
         (DList.DCons v
              (DList.DNil _)))). (**r defines a function : args -> block *)
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, store_mem_reg, State.store_mem_reg, Mem.storev, INV, app.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  get_invariant _v.
  unfold eval_inv in *.
  unfold is_state_handle in c.
  unfold match_chunk in c0.
  unfold val_ptr_correct in c1.
  unfold val64_correct in c2.
  destruct c2 as (Hc1_eq & vl & Hvl_eq).
  subst.

  unfold rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z in p1.
  unfold match_res.
  unfold vlong_to_vint_or_vlong.
  destruct ck; try constructor.
  all: destruct v2; try constructor.
  all: destruct Mem.store eqn: Hstore; [| constructor].
  all: eapply store_reg_preserive_match_state in MS as Hstore_m2; eauto.
  all: destruct Hstore_m2 as (m2 & Hstore_m2 & Hmatch_m2).
  all: intros; exists Vundef, m2, Events.E0.
  - (**r c = Mint8unsigned *)
    split_and;auto.
    + forward_star.
    change (Int.unsigned (Int.repr 1)) with 1%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
  - (**r c = Mint16unsigned *)
    split_and; auto.
    + forward_star.
    change (Int.unsigned (Int.repr 2)) with 2%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
  - (**r c = Mint32 *)
    split_and;auto.
    + forward_star.
    change (Int.unsigned (Int.repr 4)) with 4%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
  - (**r c = Mint64 *)
    split_and; auto.
    + forward_star.
    change (Int.unsigned (Int.repr 8)) with 8%Z.
    simpl.
    unfold step2.
    repeat forward_star.
    + constructor.
    + exact I.
Qed.

End Store_mem_reg.

Existing Instance correct_function_store_mem_reg.
