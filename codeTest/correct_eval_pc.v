From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CommonLemma interpreter.

(**
static unsigned long long eval_pc (struct bpf_state* st) {
  return ( *st).state_pc;
}


Definition eval_pc: M int64_t := fun st => Some (eval_pc st, st).
 *)

Definition int64_correct (x:int64_t) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
  Vlong x = v.

Section Eval_pc.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (int64_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.eval_pc.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_pc.

  Definition modifies : list block := [state_block]. (* of the C code *)
  (* [match_mem] related the Coq monadic state and the C memory *)
  (*Definition match_mem : stateM -> val -> Memory.Mem.mem -> Prop := fun stM v m => match_meminj_state state_block inject_id stM m.*)


  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => int64_correct x v st m.

  Lemma correct_function3_eval_pc : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
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
    destruct c as (H_st & Hst_casted).
    unfold stateM_correct in H_st.
    destruct H_st as (Hv_eq & Hst).
    subst v.

    (** we need to get the value of pc in the memory *)
    destruct Hst; clear minj mregs mflags mperm.
    unfold Mem.loadv in mpc.
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type of eval_pc:
         unsigned long long eval_pc (struct bpf_state* st)
       1. return value should be Vlong
       2. the memory is same
      *)
    exists (Vlong (pc_loc st)), m, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      (** TODO: adding Sreturn  more info by Ltac2 *)
      eapply Smallstep.plus_one; eauto.
      econstructor; eauto.
      do 2 econstructor; eauto.
      simpl.
      do 3 econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      reflexivity.
      reflexivity.
      unfold Coqlib.align; rewrite Ptrofs.add_zero.
      unfold Ptrofs.zero; simpl.
      rewrite Ptrofs.unsigned_repr.
      rewrite <- mpc; reflexivity.
      unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
      Transparent Archi.ptr64.
      simpl.
      lia.
      econstructor; eauto.
    - simpl.
      constructor.
  Qed.

End Eval_pc.
