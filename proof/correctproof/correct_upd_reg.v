From bpf.comm Require Import Regs State Monad.
From bpf.src Require Import DxValues DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory Memdata.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.


(**
Check upd_reg.
upd_reg
     : reg -> val64_t -> M unit
 *)


Section Upd_reg.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(reg:Type);val64_t].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.upd_reg.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_reg.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons (stateless reg_correct)
        (DList.DCons (stateless val64_correct)
          (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun _ v st m => match_state state_block mrs_block ins_block st m /\ v = Vundef.

  Instance correct_function3_upd_reg : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant_more _st.
    get_invariant_more _i.
    get_invariant_more _v.
    unfold stateM_correct in H0.
    unfold stateless, reg_correct in H2.
    unfold stateless, val64_correct in H4.
    destruct H0 as (Hv_eq & Hst).
    destruct H4 as (Hc_eq & (vl & Hvl_eq)).
    subst.

    simpl in c.
    apply (upd_regs_store m _ _ _ _ c vl) in Hst as Hstore.
    destruct Hstore as (m1 & Hstore).

    (**according to the type:
         static void upd_reg (struct bpf_state* st, unsigned int i, unsigned long long v)
       1. return value should be Vundef (i.e. void)
       2. the new memory should change the value of reg, i.e. m_reg
      *)
    exists Vundef, m1, Events.E0.

    split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.

      unfold Coqlib.align; simpl.
      rewrite Ptrofs.add_zero_l.
      assert (Heq: (8 + 8 * id_of_reg c)%Z = (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 8) (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (Int.repr (id_of_reg c))))))). {
        unfold Ptrofs.add, Ptrofs.mul.
        unfold id_of_reg; destruct c; try unfold Ptrofs.of_intu, Ptrofs.of_int; repeat rewrite Ptrofs.unsigned_repr; try rewrite Int.unsigned_repr; try rewrite Int_max_unsigned_eq64; try rewrite Ptrofs_max_unsigned_eq32; try lia.
      }
      rewrite <- Heq.
      rewrite <- Hstore; reflexivity.
    - split.
      split.
      eapply upd_reg_preserves_match_state.
      apply Hst.
      reflexivity.
      apply Hstore.
      reflexivity.
      split.

      + intros.
        simpl.
        constructor.
      + unfold unmodifies_effect, modifies, In.
        intros.
        destruct (Pos.eq_dec state_block b).
        subst b.
        exfalso.
        apply H0.
        left; reflexivity.
        apply POrderedType.PositiveOrder.neq_sym in n.
        symmetry.
        apply (Mem.load_store_other AST.Mint64 m _ _ _ m1 Hstore chk _ _).
        left; assumption.
Qed.

End Upd_reg.

Existing Instance correct_function3_upd_reg.
