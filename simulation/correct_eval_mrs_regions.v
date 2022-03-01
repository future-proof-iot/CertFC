From bpf.comm Require Import MemRegion State Monad.
From Coq Require Import List Lia.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.
Require Import ZArith.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

(**
static struct memory_region *eval_mrs_regions(struct bpf_state* st){
  return ( *st).mrs;
}

Print eval_mrs_regions.
eval_mrs_regions = 
fun st : stateM => Some (DxState.eval_mem_regions st, st)
     : M MyMemRegionsType

*)

Section Eval_mrs_regions.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [].
  Definition res : Type := (MyMemRegionsType:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_mrs_regions.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_mrs_regions.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    (DList.DCons stateM_correct
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun re v st m => re = (bpf_mrs st) /\ match_region_list state_block mrs_block ins_block  re v st m /\ match_state state_block mrs_block ins_block st m.

  Instance correct_function3_eval_mrs_regions : forall a, correct_function3 p args res f fn (nil) false match_arg_list match_res a.
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
    destruct Hst'. clear - Hst p0 mem_regs.

    eexists. exists m, Events.E0.

    split.
    {
      repeat forward_star.

      rewrite Ptrofs.add_zero_l.
      unfold Coqlib.align, AST.Mptr; simpl.

      destruct mem_regs as (mem_regs & _).
      rewrite <- mem_regs.
      unfold AST.Mptr.
      simpl.
      reflexivity.
      reflexivity.
    }
    split.
    {
      unfold match_res.
      split.
      unfold State.eval_mem_regions.
      reflexivity.
      split;[ | assumption].
      unfold match_region_list, Ptrofs.zero, State.eval_mem_regions.
      split; [reflexivity |].
      split; [reflexivity |].
      destruct mem_regs as ( _ & Hmrs).
      unfold match_regions in Hmrs.
      destruct Hmrs as (Hlen & _ & Hmrs).
      split; assumption.
    }

    split.
    simpl.
    constructor.
    simpl.
    split; reflexivity.
  Qed.

End Eval_mrs_regions.

Existing Instance correct_function3_eval_mrs_regions.
