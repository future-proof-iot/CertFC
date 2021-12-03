From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState StateBlock CommonLemma interpreter.

(**
static void upd_pc(struct bpf_state* st, unsigned long long pc) {
  ( *st).state_pc = pc;
  return ;
}
Definition upd_pc (p: int64_t): M unit := fun st => Some (tt, upd_pc p st).
 *)

Definition int64_correct (x:int64_t) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  Vlong x = v.

Section Upd_pc.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64_t:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.upd_pc.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_pc.

  Definition modifies : list block := [state_block]. (* of the C code *)
  (* [match_mem] related the Coq monadic state and the C memory *)
  (*Definition match_mem : stateM -> val -> Memory.Mem.mem -> Prop := fun stM v m => match_meminj_state state_block inject_id stM m.*)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state_block stm state_block m.

(**
Mem.store AST.Mint64 m state_block 0 (Vlong c) = Some ?m'
*)

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DCons int64_correct (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun _ _ _ _ => True.

  Lemma correct_function3_upd_pc : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof. (*
    eapply correct_function_from_body.
    - simpl; unfold Coqlib.list_disjoint; simpl; intuition (subst; discriminate).
    - eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    - simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity.
    - reflexivity.
    - reflexivity.*)
    eapply correct_function_from_body;
    [ simpl; unfold Coqlib.list_disjoint; simpl; intuition (subst; discriminate) |
      eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
      simpl; eapply list_no_repet_dec with (eq_dec := Pos.eq_dec); reflexivity |
      reflexivity |
      reflexivity |
      idtac
    ].
    intros.
    unfold args in *.
    car_cdr.
    unfold list_rel_arg.
    simpl.
    unfold correct_body.
    repeat intro.
    get_invariant _st.
    get_invariant _pc.
    destruct c0 as (H_st & Hst_casted).
    destruct c1 as (H_pc & Hpc_casted).
    unfold stateM_correct, match_state_block in H_st.
    unfold int64_correct in H_pc.
    (*destruct H_st as (Hv_eq & (pc & Hpc_ld) & Hpc_st & (regs_blk & Hregs_blk_mem) & Hregs_st & (flag & Hflag_mem) & Hflag_st & (mrs_blk & Hmrs_blk_mem) & Hmrs_st). *)
    destruct H_st as (Hv_eq & (pc & Hpc_ld) & Hpc_st & _).
    subst v0 v.
    
    specialize (Hpc_st (Vlong c)).
    destruct Hpc_st as (m_pc & Hpc_st).

    unfold pre in *.
    (**according to the type of upd_pc:
         static void upd_pc(struct bpf_state* st, unsigned long long pc)
       1. return value should be Vundef (i.e. void)
       2. the new memory should change the value of pc, i.e. m_pc
      *)
    exists Vundef, m_pc, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      repeat forward_plus.

      eapply Smallstep.plus_left'; eauto.
      econstructor; eauto.
      do 4 econstructor; eauto.
      eapply eval_Etempvar; rewrite p1; reflexivity.
      reflexivity.
      econstructor; eauto; reflexivity.
      eforward_plus.
      eapply Smallstep.plus_one; eauto.
      eapply step_return_0.
      reflexivity.
      reflexivity.
    - simpl.
      constructor.
    - unfold unmodifies_effect, modifies, In.
      intros.
      symmetry.
      apply (Mem.load_store_other AST.Mint64 m state_block 0%Z (Vlong c) m_pc Hpc_st).
      left.
      intuition.
Qed.

End Upd_pc.
