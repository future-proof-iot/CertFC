From bpf.comm Require Import Regs State Monad.
From bpf.src Require Import DxNat DxOpcode DxIntegers DxInstructions.
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
  Definition args : list Type := [(nat8:Type)].
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
    (DList.DCons (stateless opcode_alu64_nat8_correct)
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
    get_invariant_more _op.

    unfold stateless, opcode_alu64_nat8_correct in H0.
    destruct H0 as (H0 & Hland & Hge).
    subst.

    eexists. exists m, Events.E0.

    repeat split; unfold step2.
    -
      repeat forward_star.
    - simpl.
      (**r Search (Int.zero_ext).*)
      rewrite Int.zero_ext_idem;[idtac | lia].
      unfold match_res, opcode_alu64_correct.
      rewrite byte_to_opcode_alu64_if_same.
      unfold byte_to_opcode_alu64_if.
      rewrite Int.zero_ext_and; [simpl | lia].
      rewrite nat8_land_240_255_eq; [| apply Hge].

Ltac simpl_if Ht :=
  match goal with
  | |- context [if ?X then _ else _] =>
    destruct X eqn: Ht; [rewrite Nat.eqb_eq in Ht | rewrite Nat.eqb_neq in Ht]
  end.

Ltac simpl_alu_opcode Hop := simpl_if Hop; [rewrite Hop; reflexivity | ].

      simpl_alu_opcode Hadd.
      simpl_alu_opcode Hsub.
      simpl_alu_opcode Hmul.
      simpl_alu_opcode Hdiv.
      simpl_alu_opcode Hor.
      simpl_alu_opcode Hand.
      simpl_alu_opcode Hlsh.
      simpl_alu_opcode Hrsh.
      simpl_if Hneg.
      destruct (c =? 135)%nat eqn: Hc_eq; [rewrite Nat.eqb_eq in Hc_eq; rewrite Hc_eq; reflexivity | eexists; reflexivity].
      simpl_alu_opcode Hmod.
      simpl_alu_opcode Hxor.
      simpl_alu_opcode Hmov.
      simpl_alu_opcode Harsh.
      eexists; reflexivity.
    - simpl.
      constructor.
      rewrite Int.zero_ext_idem;[idtac | lia].
      simpl.
      rewrite Int.zero_ext_idem;[idtac | lia].
      reflexivity.
Qed.

End Get_opcode_alu64.

Existing Instance correct_function3_get_opcode_alu64.
