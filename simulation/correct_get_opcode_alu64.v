From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLemmaNat.

From bpf.clight Require Import interpreter.


(**
Check get_opcode_alu64.
get_opcode_alu64
     : int8_t -> M DxOpcode.opcode_alu64

*)

Section Get_opcode_alu64.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode_alu64:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_opcode_alu64.

  Variable state_block: block. (**r a block storing all rbpf state information? *)
  Variable mrs_block: block.
  Variable ins_block: block.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_alu64.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless opcode_and_07_correct)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => opcode_alu64_correct x v.

  Instance correct_function3_get_opcode_alu64 : forall a, correct_function3 p args res f fn nil true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _op.

    unfold stateless, opcode_and_07_correct in c0.
    destruct c0 as (H0 & Hge & Hland7).
    subst.

    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.
    - simpl.
      (**r Search (Int.zero_ext).*)
      rewrite Int.zero_ext_idem;[idtac | lia].
      rewrite Int.zero_ext_and; [| lia].
      rewrite nat8_land_240_255_eq; [| apply Hge].
      unfold match_res, opcode_alu64_correct.
      rewrite byte_to_opcode_alu64_if_same.
      unfold byte_to_opcode_alu64_if.

      simpl_opcode Hadd.
      simpl_opcode Hsub.
      simpl_opcode Hmul.
      simpl_opcode Hdiv.
      simpl_opcode Hor.
      simpl_opcode Hand.
      simpl_opcode Hlsh.
      simpl_opcode Hrsh.
      simpl_opcode Hneg. (*
      simpl_if Hneg.
      destruct (c =? 135)%nat eqn: Hc_eq; [rewrite Nat.eqb_eq in Hc_eq; rewrite Hc_eq; exists; reflexivity |rewrite Nat.eqb_neq in Hc_eq].
      rewrite nat_land_240_eq_128 in Hneg; auto.
      assert (Hc: c = 143). {
        destruct Hneg.
        intuition.
        assumption.
      }
      exists 143.
      split; [rewrite Hc; reflexivity |].
      unfold is_illegal_alu64_ins.
      lia. (*
      assert (Hci_eq : Nat.land c 240 = Nat.land i 240). {
        clear - H0.
        remember (Nat.land c 240) as C.
        remember (Nat.land i 240) as I.
        assert (Hlec: C <= 240) by (rewrite HeqC; rewrite Nat.land_comm; apply LemmaNat.land_bound).
        assert (Hlei: I <= 240) by (rewrite HeqI; rewrite Nat.land_comm; apply LemmaNat.land_bound).
        assert (Hle_c: (Z.of_nat C <= 240)%Z) by (rewrite HeqC; lia).
        assert (Hle_i: (Z.of_nat I <= 240)%Z) by (rewrite HeqI; lia).
        assert (Hvint_eq: forall i j, Vint i = Vint j <-> i = j). {
          intros.
          split; intro Hvint.
          inversion Hvint; reflexivity.
          rewrite Hvint; reflexivity.
        }
        rewrite Hvint_eq in H0; clear Hvint_eq.
        apply Int_repr_eq in H0; change Int.max_unsigned with 4294967295%Z; lia.
      }*)
      (*
      exists c; split; [reflexivity| idtac].
      unfold is_illegal_alu64_ins.
      repeat simpl_land H0.
      assumption. *)
      (*
      assert (Hc_eq_135 : c = 0x8f). {
        (**according to the fact: Nat.land c 7 = 7 /\ Nat.land c 240 = 128, we should know c = 0x87 (i.e. 135) \/ c = 0x8f (i.e. 143)*)
        admit.
      }
      Compute (Nat.land 143 240). *) *)

      simpl_opcode Hmod.
      simpl_opcode Hxor.
      simpl_opcode Hmov.
      simpl_opcode Harsh.
      exists c; split; [reflexivity| idtac].
      unfold is_illegal_alu64_ins.
      repeat simpl_land H0.
(*
Ltac Hc_neq H0 :=
  match goal with
  | |- ?C <> ?X =>
    let r := eval compute in (Nat.land X 240) in
    destruct (C =? X) eqn : Hc_eq;[
        rewrite Nat.eqb_eq in Hc_eq;
        rewrite Hc_eq in H0;
        change (Nat.land X 240) with r in H0;
        lia | rewrite Nat.eqb_neq in Hc_eq; assumption
    ]
  | |- ?C <> ?X /\ _ =>
    let r := eval compute in (Nat.land X 240) in
    destruct (C =? X) eqn : Hc_eq;[
        rewrite Nat.eqb_eq in Hc_eq;
        rewrite Hc_eq in H0;
        change (Nat.land X 240) with r in H0;
        lia | rewrite Nat.eqb_neq in Hc_eq; split; [assumption | clear Hc_eq]
    ]
  end.
      do 2 Hc_neq Hadd.
      do 2 Hc_neq Hsub.
      do 2 Hc_neq Hmul.
      do 2 Hc_neq Hdiv.
      do 2 Hc_neq Hor.
      do 2 Hc_neq Hand.
      do 2 Hc_neq Hlsh.
      do 2 Hc_neq Hrsh.
      Hc_neq Hneg.
      do 2 Hc_neq Hmod.
      do 2 Hc_neq Hxor.
      do 2 Hc_neq Hmov.
      do 2 Hc_neq Harsh. *)
    - simpl.
      constructor.
      rewrite Int.zero_ext_idem;[idtac | lia].
      simpl.
      rewrite Int.zero_ext_idem;[idtac | lia].
      reflexivity.
Qed.

End Get_opcode_alu64.

Existing Instance correct_function3_get_opcode_alu64.
