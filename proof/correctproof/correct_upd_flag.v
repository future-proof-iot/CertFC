From bpf.comm Require Import Flag State Monad.
From bpf.src Require Import DxValues DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.


(**
Check upd_flag.
upd_flag
     : DxFlag.bpf_flag -> M unit
*)

Section Upd_flag.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(bpf_flag:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.upd_flag.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_flag.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
                (DList.DCons (stateless flag_correct)
                             (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef.

  Instance correct_function3_upd_flag : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant_more _st.
    get_invariant_more _f.
    unfold stateM_correct in H0.
    unfold stateless, flag_correct in H2.
    destruct H0 as (Hv_eq & Hst).
    subst.

    simpl in c.
    assert (Hst2 := Hst).
    apply (upd_flags_store _ _ _ _ _ (int_of_flag c)) in Hst2 as Hstore.
    destruct Hstore as (m1 & Hstore).
    (** we need to get the value of flag in the memory *)
    set (Hst' := Hst).
    destruct Hst' as (_, _ , Hflag, _, _, _, _, _, _, _).
    unfold Mem.loadv in Hflag.
    
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static void upd_flag(struct bpf_state* st, int f)
       1. return value should be Vundef
       2. the memory is m_flag
      *)
    exists Vundef, m1, Events.E0.

    split; unfold step2.
    - repeat forward_star.
    - split.
      split.
      eapply upd_flag_preserves_match_state.
      apply Hst.
      reflexivity.
      apply Hstore.
      reflexivity.
      split.

      simpl.
      constructor.

      unfold unmodifies_effect.
      simpl.
      intros.
      destruct (Pos.eq_dec state_block b).
      subst b.
      exfalso.
      apply H0.
      left; reflexivity.
      apply POrderedType.PositiveOrder.neq_sym in n.
      symmetry.
      apply (Mem.load_store_other AST.Mint32 m _ _ _ m1 Hstore chk _ _).
      left; assumption.
  Qed.

End Upd_flag.

Existing  Instance correct_function3_upd_flag.
