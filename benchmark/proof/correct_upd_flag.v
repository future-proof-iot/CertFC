From bpf.src Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxFlag DxInstructions.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.
From bpf.benchmark Require Import clightlogicexample.

(**

static void upd_flag(struct bpf_state* st, int f){
  ( *st).bpf_flag = f;
  return ;
}

Definition upd_flag (f:bpf_flag) : M unit := fun st => Some (tt, upd_flag f st).
*)

Section Upd_flag.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(bpf_flag:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.upd_flag.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_flag.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
                (DList.DCons (stateless flag_correct)
                             (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => True.

  Instance correct_function3_upd_flag : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant_more _st.
    get_invariant_more _f.
    unfold stateM_correct in H1.
    unfold stateless, flag_correct in H3.
    destruct H1 as (Hv_eq & Hst).
    subst v v0.

    simpl in c.
    apply (upd_flags_store _ _ _ (int_of_flag c)) in Hst as Hstore.
    destruct Hstore as (m1 & Hstore).
    (** we need to get the value of flag in the memory *)
    destruct Hst; clear minj mpc mregs mperm.
    unfold Mem.loadv in mflags.
    unfold size_of_regs in mflags; simpl in mflags.
    
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static void upd_flag(struct bpf_state* st, int f)
       1. return value should be Vundef
       2. the memory is m_flag
      *)
    exists Vundef, m1, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      repeat forward_clight.

      reflexivity.
    - simpl.
      constructor.
    -
      unfold unmodifies_effect.
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

End Upd_flag.

Existing  Instance correct_function3_upd_flag.