From dx.tests Require Import DxIntegers DxValues DxMemRegion DxState DxMonad DxFlag DxInstructions.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma interpreter.

(**
static int eval_flag(struct bpf_state* st){
  return ( *st).bpf_flag;
}

Definition eval_flag : M bpf_flag := fun st => Some (eval_flag st, st).
*)

Section Eval_flag.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (bpf_flag:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := DxMonad.eval_flag.

  Variable state_block: block. (**r a block storing all rbpf state information? *)

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_flag.

  Definition modifies : list block := [state_block]. (* of the C code *)

  Definition stateM_correct (st:unit) (v: val) (stm:stateM) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop := fun x v st m => flag_correct x v.

  Instance correct_function3_eval_flag : correct_function3 p args res f fn modifies false match_arg_list match_res.
  Proof.
    correct_function_from_body.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    destruct c as (H_st & Hst_casted).
    unfold stateM_correct in H_st.
    destruct H_st as (Hv_eq & Hst).
    subst v.

    (** we need to get the value of pc in the memory *)
    destruct Hst; clear minj mpc mregs mperm.
    unfold Mem.loadv in mflags.
    unfold size_of_regs in mflags; simpl in mflags.
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static int eval_flag(struct bpf_state* st)
       1. return value should be Vint
       2. the memory is same
      *)
    exists (Vint (int_of_flag (flag st))), m, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      apply Smallstep.plus_star.
      forward_plus.
      repeat (econstructor; eauto; try deref_loc_tactic).
      unfold Coqlib.align; simpl.
      rewrite Ptrofs.add_zero_l.
      rewrite mflags; reflexivity.
      econstructor; eauto.
      reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Eval_flag.

Existing  Instance correct_function3_eval_flag.
