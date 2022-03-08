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

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) ((unit:Type) ::args) :=
    DList.DCons (stateM_correct state_block mrs_block ins_block)
      (DList.DCons (stateless int32_correct)
        (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => int64_correct x v.

  Instance correct_function3_eval_ins : forall a, correct_function3 p args res f fn nil false match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold f; simpl.
    destruct eval_ins eqn: Heval_ins; [| constructor].
    destruct p0.
    intros.
    unfold INV in H.
    get_invariant _st.
    get_invariant _idx.
    unfold stateM_correct in c0.
    destruct c0 as (Hv_eq & Hst).
    unfold stateless, int32_correct in c1.
    subst.

    (** we need to get the value of pc in the memory *)
    destruct Hst. clear - p0 p1 Heval_ins mins_len mins.
    destruct mins_len as (Hload_eq & Hge).
    destruct mins as (Hins_eq & Hlen & Hle & Hmatch).
    eexists; exists m, Events.E0.

    split.
    {
      unfold step2.
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
      unfold Ptrofs.of_intu, Ptrofs.of_int.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
      change Ptrofs.max_signed with 2147483647%Z in Hle.
      unfold eval_ins in Heval_ins.
      context_destruct_if_inversion.
      unfold Int.cmp in Hcond.
      simpl in c.
      rewrite Bool.andb_true_iff in Hcond.
      destruct Hcond as (Hlow & Hhigh).
      apply Cle_Zle_unsigned in Hlow.
      apply Clt_Zlt_unsigned in Hhigh.
      change (Int.unsigned Int.zero) with 0%Z in Hlow.
      rewrite Int.unsigned_repr in Hhigh. 2:{
        change Int.max_unsigned with 4294967295%Z.
        lia.
      }
      rewrite Ptrofs.unsigned_repr with (z:= (Int.unsigned c)); [| change Ptrofs.max_unsigned with 4294967295%Z; lia].
      rewrite Ptrofs.unsigned_repr; [| change Ptrofs.max_unsigned with 4294967295%Z; lia].
      rewrite Hlen in Hmatch.
      assert (Hnat: (0 <= Z.to_nat (Int.unsigned c) < ins_len st)%nat) by lia.
      specialize (Hmatch _ Hnat); clear Hnat.
      unfold Mem.loadv in Hmatch.
      assert (Hnat: Z.of_nat (Z.to_nat (Int.unsigned c)) = Int.unsigned c). { apply Z2Nat.id. lia. }
      rewrite Hnat in Hmatch; clear Hnat.
      rewrite Ptrofs.unsigned_repr in Hmatch; [| change Ptrofs.max_unsigned with 4294967295%Z; lia].
      subst.
      apply Hmatch.
      unfold Cop.sem_cast, typeof; simpl.
      reflexivity.
      forward_star.
    }
    split.
    {
      unfold match_res, int64_correct.
      unfold eval_ins in Heval_ins.
      context_destruct_if_inversion.
      unfold State.eval_ins, List64.MyListIndexs32, List64.MyList.index_s32.
      reflexivity.
    }
    split.
    constructor.
    split; [reflexivity |].
    unfold eval_ins in Heval_ins.
    context_destruct_if_inversion.
    reflexivity.
  Qed.

End Eval_ins.

Existing  Instance correct_function3_eval_ins.
