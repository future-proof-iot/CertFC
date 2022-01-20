From bpf.comm Require Import Flag State Monad.

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLib.

From bpf.clight Require Import interpreter.


(**
Check eval_flag.
eval_flag
     : M DxFlag.bpf_flag
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
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_flag.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => flag_correct x v.

  Instance correct_function3_eval_flag : forall a, correct_function3 p args res f fn [] false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    destruct c as (H_st & Hst_casted).
    unfold stateM_correct in H_st.
    destruct H_st as (Hv_eq & Hst).
    subst.

    (** we need to get the value of pc in the memory *)
    destruct Hst.
    clear munchange mpc mregs mperm.
    unfold Mem.loadv in mflags.
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static int eval_flag(struct bpf_state* st)
       1. return value should be Vint
       2. the memory is same
      *)
    exists (Vint (int_of_flag (flag st))), m, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.

      unfold Coqlib.align; simpl.
      rewrite Ptrofs.add_zero_l.
      rewrite mflags; reflexivity.
      econstructor; eauto.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Eval_flag.

Existing  Instance correct_function3_eval_flag.
