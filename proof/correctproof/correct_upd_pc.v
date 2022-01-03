From bpf.src Require Import DxIntegers DxValues DxMonad DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check upd_pc.
upd_pc
     : sint32_t -> M unit
 *)

Section Upd_pc.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(sint32_t:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.upd_pc.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_pc.

  Definition modifies : list block := [state_block]. (* of the C code *)
  
  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
                (DList.DCons (stateless sint32_correct)
                             (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun _ _ _ _ => True.

  Instance correct_function3_upd_pc : forall a, correct_function3 p args res f fn modifies false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant_more _st.
    get_invariant_more _pc.
    unfold stateM_correct in H1.
    unfold stateless, sint32_correct in H3.
    destruct H1 as (Hv_eq & Hst).
    (*pose (mpc_store state_block st m Hst c (bpf_m st)). *)   
    subst.
    
    (** we need to get the proof of `upd_pc` store permission *)
    apply (upd_pc_store _ _ c _) in Hst as Hstore.
    destruct Hstore as (m1 & Hstore).
    (** pc \in [ (state_block,0), (state_block,8) ) *)

    simpl in c.
    (**according to the type of upd_pc:
         static void upd_pc(struct bpf_state* st, unsigned long long pc)
       1. return value should be Vundef (i.e. void)
       2. the new memory should change the value of pc, i.e. m_pc
      *)
    exists Vundef, m1, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.
    - simpl.
      constructor.
    - unfold unmodifies_effect, modifies, In.
      intros.
      destruct (Pos.eq_dec state_block b).
      subst b.
      exfalso.
      apply H1.
      left; reflexivity.
      apply POrderedType.PositiveOrder.neq_sym in n.
      symmetry.
      apply (Mem.load_store_other AST.Mint32 m _ _ _ m1 Hstore chk _ _).
      left; assumption.
Qed.

End Upd_pc.

Existing Instance correct_function3_upd_pc.