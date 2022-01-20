From bpf.comm Require Import State Monad.
From bpf.src Require Import DxIntegers.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check eval_pc.
eval_pc
     : M sint32_t
*)

Section Eval_pc.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (sint32_t:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := Monad.eval_pc.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_pc.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => sint32_correct x v.

  Instance correct_function3_eval_pc : forall a, correct_function3 p args res f fn nil false match_arg_list match_res a.
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
    destruct Hst; clear munchange mregs mflags mperm.
    unfold Mem.loadv in mpc.
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type of eval_pc:
         unsigned long long eval_pc (struct bpf_state* st)
       1. return value should be Vlong
       2. the memory is same
      *)
    exists (Vint (pc_loc st)), m, Events.E0.

    repeat split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.

      unfold Coqlib.align; rewrite Ptrofs.add_zero.
      unfold Ptrofs.zero; simpl.
      rewrite Ptrofs.unsigned_repr.
      rewrite <- mpc; reflexivity.
      rewrite Ptrofs_max_unsigned_eq32.
      lia.
      reflexivity.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Eval_pc.

Existing  Instance correct_function3_eval_pc.
