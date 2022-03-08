From bpf.comm Require Import MemRegion State Monad.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
static __attribute__((always_inline)) inline unsigned int eval_mrs_num(struct bpf_state* st){
  return ( *st).mrs_num;
}

Print eval_mrs_num.
eval_mrs_num = fun st : State.state => Some (eval_mem_num st, st)
     : M nat

*)

Section Eval_mrs_num.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [].
  Definition res : Type := (nat:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_mrs_num.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_mrs_num.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons (stateM_correct state_block mrs_block ins_block)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun re v st m => nat_correct re v /\ re = (mrs_num st) /\ match_state state_block mrs_block ins_block st m.

  Instance correct_function3_eval_mrs_num : forall a, correct_function3 p args res f fn (nil) false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _st.

    unfold stateM_correct in c.
    destruct c as (Hv_eq & Hst).
    subst v.

    assert (Hst' := Hst).
    destruct Hst'. clear - Hst p0 mmrs_num.

    eexists. exists m, Events.E0.

    split.
    {
      repeat forward_star.
      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align; simpl.

      destruct mmrs_num as (mmrs_num & _).
      unfold Mem.loadv in mmrs_num.
      rewrite mmrs_num.
      reflexivity.
      reflexivity.
    }
    split.
    {
      unfold match_res.
      split.
      - unfold nat_correct, eval_mem_num.
        reflexivity.
      - split.
        unfold eval_mem_num.
        reflexivity.
        assumption.
    }

    split; [simpl; constructor; reflexivity | split; reflexivity].
  Qed.

End Eval_mrs_num.

Existing Instance correct_function3_eval_mrs_num.
