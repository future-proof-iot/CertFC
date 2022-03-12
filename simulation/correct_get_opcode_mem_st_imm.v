From bpf.comm Require Import Regs State Monad LemmaNat.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

(**
Check get_opcode_mem_st_imm
get_opcode_mem_st_imm
     : nat -> M opcode_mem_st_imm

*)

Open Scope nat_scope.

Section Get_opcode_mem_st_imm.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode_mem_st_imm:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_opcode_mem_st_imm.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_mem_st_imm.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) args :=
    (dcons (fun x => StateLess (opcode_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x  => StateLess (opcode_mem_st_imm_correct x).

  Instance correct_function_get_opcode_mem_st_imm : forall a, correct_function p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _op.

    unfold eval_inv, opcode_correct in c0.
    destruct c0 as (Hc_eq & Hc_range).
    subst.

    eexists. exists m, Events.E0.
    unfold byte_to_opcode_mem_st_imm.
    split_and; unfold step2; auto.
    -
      forward_star.
      simpl.
      rewrite Int.zero_ext_idem; [| lia].
      rewrite Int.zero_ext_and; [| lia].
      change (two_p 8 - 1)%Z with 255%Z.
      rewrite Int.and_assoc.
      rewrite Int.and_idem.
      forward_star.
    -
      unfold match_res, opcode_mem_st_imm_correct.
      rewrite Nat_land_0xff; auto.
      destruct (c =? 98) eqn: Hstw;
      [rewrite Nat.eqb_eq in Hstw; subst; reflexivity | rewrite Nat.eqb_neq in Hstw].
      destruct (c =? 106) eqn: Hsth;
      [rewrite Nat.eqb_eq in Hsth; subst; reflexivity | rewrite Nat.eqb_neq in Hsth].
      destruct (c =? 114) eqn: Hstb;
      [rewrite Nat.eqb_eq in Hstb; subst; reflexivity | rewrite Nat.eqb_neq in Hstb].
      destruct (c =? 122) eqn: Hstdw;
      [rewrite Nat.eqb_eq in Hstdw; subst; reflexivity | rewrite Nat.eqb_neq in Hstdw].

      assert (Hswitch:
          match c with
          | 98 => op_BPF_STW
          | 106 => op_BPF_STH
          | 114 => op_BPF_STB
          | 122 => op_BPF_STDW
          | _ => op_BPF_ST_ILLEGAL_INS
          end = op_BPF_ST_ILLEGAL_INS). {
          do 98 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hstw; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hsth; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hstb; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hstdw; reflexivity | reflexivity].
        }
        rewrite Hswitch; clear Hswitch.
        exists c.
        split; [ | intuition ].
        unfold Int.and.
        change (Int.unsigned (Int.repr 255)) with (Z.of_nat (Z.to_nat 255%Z)).
        rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
        rewrite LemmaNat.land_land.
        change (Z.to_nat 255) with 255.
        rewrite Nat_land_0xff; auto.
    - constructor.
      simpl.
      rewrite Int.zero_ext_and.
      change (two_p 8 - 1)%Z with 255%Z.
      rewrite Int.and_assoc.
      rewrite Int.and_idem.
      reflexivity.
      lia.
    - apply unmodifies_effect_refl.
  Qed.

End Get_opcode_mem_st_imm.

Close Scope nat_scope.

Existing Instance correct_function_get_opcode_mem_st_imm.
