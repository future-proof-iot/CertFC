From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CommonLemma interpreter.

(**
static void upd_pc(struct bpf_state* st, unsigned long long pc) {
  ( *st).state_pc = pc;
  return ;
}
Definition upd_pc (p: int64_t): M unit := fun st => Some (tt, upd_pc p st).
 *)

(*
Ltac forward_seq :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | idtac]
  end.

Ltac forward_call_one_arg :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_call; [reflexivity | eapply eval_Elvalue;[eapply eval_Evar_global; reflexivity | eapply deref_loc_reference; reflexivity] | eapply eval_Econs; [eapply eval_Etempvar; reflexivity | reflexivity | eapply eval_Enil] | econstructor; eauto | reflexivity] | idtac]
  end.

Ltac forward_returnstate :=
  match goal with
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | idtac]
  end.

Ltac forward_skip_seq :=
  match goal with
  | |- Smallstep.plus _ _ (State _ Sskip (Kseq _ _) _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | idtac]
  end.

Ltac forward_if :=
  match goal with
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
  eapply Smallstep.plus_left'; eauto; [eapply step_ifthenelse; [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity | reflexivity] | idtac]
  end.*)

Ltac forward_plus :=
 match goal with
  (** forward_seq *)
  | |- Smallstep.plus _ _ (State _ (Ssequence _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_seq | idtac]
  (** forward_call_one_arg *)
  | |- Smallstep.plus _ _ (State _ (Scall _ _ _) _ _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto;
      [eapply step_call;
        [reflexivity |                                (** goal: classify_fun *)
         eapply eval_Elvalue;                         (** goal: eval_expr *)
          [eapply eval_Evar_global; reflexivity |     (** eval_lvalue *)
           eapply deref_loc_reference; reflexivity] | (** goal: deref_loc *)
         eapply eval_Econs;                           (** goal: eval_exprlist *)
          [eapply eval_Etempvar; reflexivity |        (** goal: eval_expr *)
           reflexivity |                              (** goal: Cop.sem_cast *)
           eapply eval_Enil] |                        (** goal: eval_exprlist *)
         econstructor; eauto |                        (** goal: Globalenvs.Genv.find_funct *)
         reflexivity] |                               (** goal: type_of_fundef *)
       idtac]
  (** forward_returnstate *)
  | |- Smallstep.plus _ _ (Returnstate _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_returnstate | idtac]
  (** forward_skip_seq *)
  | |- Smallstep.plus _ _ (State _ Sskip (Kseq _ _) _ _ _) _ _ =>
      eapply Smallstep.plus_left'; eauto; [eapply step_skip_seq | idtac]
  (** forward_if *)
  | |- Smallstep.plus _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
    [eapply step_ifthenelse;
      [eapply eval_Etempvar; rewrite Maps.PTree.gss; reflexivity |
       reflexivity] |
     idtac]
  (** forward_return_some *)
  | |- Smallstep.plus _ _ (State _ (Sreturn _) _ _ _ _) _ _ =>
    eapply Smallstep.plus_left'; eauto;
      [eapply step_return_1;
        [eapply eval_Econst_long |
         reflexivity |
         reflexivity] | idtac]
 end.

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
    v = Vptr state_block Ptrofs.zero.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DCons int64_correct (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun _ _ _ _ => True.

  Lemma correct_function3_upd_pc : correct_function3 p args res f fn modifies match_arg_list match_res.
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
    (**r unfold match_temp_env *)
    unfold match_temp_env, match_elt in H.
    rewrite Forall_forall in H.

    
    assert (Hinlist0: In (_st, Clightdefs.tptr (Ctypes.Tstruct _bpf_state Ctypes.noattr), stateM_correct tt)
        [(_st, Clightdefs.tptr (Ctypes.Tstruct _bpf_state Ctypes.noattr), stateM_correct tt);
        (_pc, Clightdefs.tulong, int64_correct c)]). {
      unfold In.
      left; reflexivity.
    }
    apply H in Hinlist0.
    assert (Hinlist1: In (_pc, Clightdefs.tulong, int64_correct c)
        [(_st, Clightdefs.tptr (Ctypes.Tstruct _bpf_state Ctypes.noattr), stateM_correct tt);
        (_pc, Clightdefs.tulong, int64_correct c)]). {
      unfold In.
      right; left; reflexivity.
    }
    apply H in Hinlist1.
    unfold fst in Hinlist0, Hinlist1.
    destruct (Maps.PTree.get _st le) eqn: Hst_get in Hinlist0; [idtac | intuition].
    destruct (Maps.PTree.get _pc le) eqn: Hpc_get in Hinlist1; [idtac | intuition].
    destruct Hinlist0 as (H_st & _).
    destruct Hinlist1 as (H_pc & _).
    simpl in H_st, H_pc.
    unfold stateM_correct in H_st.
    unfold int64_correct in H_pc.
    rewrite H_st in Hst_get.
    rewrite <- H_pc in Hpc_get.
    (*
    apply Cop.cast_val_casted with (m:=m) in Hcasted.
    unfold Cop.sem_cast in Hcasted.
    simpl in Hcasted.    *)

    
    
    unfold pre in *.
    do 3 eexists.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      repeat forward_plus.
      eapply Smallstep.plus_left'; eauto.
      + simpl in H.
        eapply step_assign. Unshelve.
        * eapply eval_Efield_struct.
          ** (* goal: eval_expr _ _ _ _ (Ederef (Etempvar ... *)
            eapply eval_Elvalue.
            ++ (* goal: eval_lvalue _ _ _ _ (Ederef (Etempvar ... *)
              eapply eval_Ederef.
              eapply eval_Etempvar.
              rewrite Hst_get; reflexivity.
            ++ (* goal: deref_loc (typeof (Ederef (Etempvar ... *)
              simpl.
              eapply deref_loc_copy. (**r TODO: why is it by-copy? *)
              reflexivity.
          ** reflexivity.
          ** reflexivity.
          ** reflexivity.
        * (* goal: eval_expr _ _ _ _ (Etempvar *)
          eapply eval_Etempvar.
          rewrite Hpc_get; reflexivity.
        *
          reflexivity.
        * (* goal: assign_loc _ (typeof (Efield (Ederef (Etempvar _st ... *)
          eapply assign_loc_value.
          ** reflexivity.
          ** 
            simpl.
            unfold Coqlib.align; simpl.
            rewrite Ptrofs.add_zero_l.
            rewrite Ptrofs.unsigned_repr.
            (*state_block: pc+... *)
          econstructor; eauto.
          reflexivity.
        *
              econstructor; eauto.
              unfold deref_loc.
              assumption.




            apply MakeMatch in Hctype.
            unfold match_meminj_state in Hctype.
            destruct H0 as (Hinlist).
      econstructor; eauto.
      
      econstructor; eauto.
      ...
      repeat intro.
     reflexivity. repeat econstructor; eauto.

  Qed.

End Upd_pc.
