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
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [].
  Definition res : Type := (nat:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_mrs_num.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_mrs_num.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess is_state_handle)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun re => StateFull (fun v st m => nat_correct re v /\ re = (mrs_num st)).

  Instance correct_function_eval_mrs_num : forall a, correct_function p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _st.
    unfold eval_inv, is_state_handle in c.
    subst.

    assert (Hst' := MS).
    destruct Hst'. clear - MS p0 mmrs_num mem_regs.

    eexists. exists m, Events.E0.

    split_and.
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
      unfold match_res, nat_correct, eval_mem_num.
      split.
      reflexivity.
      unfold match_regions in mem_regs.
      destruct mem_regs as (_ & Hlen & Hrange & _).
      rewrite Hlen in Hrange.
      change Int.max_unsigned with Ptrofs.max_unsigned.
      lia.
    }
    unfold eval_mem_num. reflexivity.
    constructor. reflexivity.
    auto.
    apply unmodifies_effect_refl.
  Qed.

End Eval_mrs_num.

Existing Instance correct_function_eval_mrs_num.
