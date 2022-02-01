From bpf.comm Require Import State Monad.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.


(**
Check eval_ins.
eval_ins
     : int -> M int64
*)

Section Eval_ins.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int:Type)].
  Definition res : Type := (int64:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_ins.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_ins.

  Definition stateM_correct (st:unit) (v: val) (stm:State.state) (m: Memory.Mem.mem) :=
    v = Vptr state_block Ptrofs.zero /\ match_state state_block mrs_block ins_block stm m.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons stateM_correct
      (DList.DCons ins_idx_correct
        (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => int64_correct x v.

  Instance correct_function3_eval_ins : forall a, correct_function3 p args res f fn nil false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    get_invariant _idx.
    unfold stateM_correct in c0.
    destruct c0 as (Hv_eq & Hst).
    unfold ins_idx_correct in c1.
    destruct c1 as (Hc_eq & Hc_range).
    (**r I should say idx is less than Int.max_signed *)
    subst.

    (** we need to get the value of pc in the memory *)
    destruct Hst. clear - p0 p1 Hc_range mins_len mins.
    destruct mins_len as (Hload_eq & Hge).
    destruct mins as (Hins_eq & Hlen & Hle & Hmatch).
    eexists; exists m, Events.E0.

    split.
    {
      forward_star.
      unfold Coqlib.align; rewrite Ptrofs.add_zero_l.
      simpl.
      unfold Mem.loadv in Hins_eq.
      apply Hins_eq.
      reflexivity.
      fold Ptrofs.zero; rewrite Ptrofs.add_zero_l.
      simpl.
      unfold match_list_ins in Hmatch.
      unfold Ptrofs.mul.
      unfold Ptrofs.of_ints.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
      rewrite Ptrofs.unsigned_repr with (z:= (Int.signed c)); [| lia].
      rewrite Ptrofs.unsigned_repr; [| lia].
      rewrite Hlen in Hmatch.
      assert (Hnat: (0 <= Z.to_nat (Int.signed c) < ins_len st)%nat). {
        lia.
      }
      specialize (Hmatch _ Hnat); clear Hnat.
      unfold Mem.loadv in Hmatch.
      assert (Hnat: Z.of_nat (Z.to_nat (Int.signed c)) = Int.signed c). { apply Z2Nat.id. lia. }
      rewrite Hnat in Hmatch; clear Hnat.
      rewrite Ptrofs.unsigned_repr in Hmatch; [| lia].
      apply Hmatch.
      reflexivity.
      forward_star.
    }
    split.
    {
      unfold match_res, State.eval_ins, int64_correct, List64.MyListIndexs32, List64.MyList.index_s32.
      reflexivity.
    }
    split.
    {
      constructor.
    }
    split; reflexivity.
  Qed.

End Eval_ins.

Existing  Instance correct_function3_eval_ins.
