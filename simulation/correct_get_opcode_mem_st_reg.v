From bpf.comm Require Import Regs State Monad LemmaNat.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

(**
Check get_opcode_mem_st_reg
get_opcode_mem_st_reg
     : nat -> M opcode_mem_st_reg

*)

Open Scope nat_scope.

Section Get_opcode_mem_st_reg.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode_mem_st_reg:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_opcode_mem_st_reg.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_mem_st_reg.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless opcode_correct)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => opcode_mem_st_reg_correct x v.

  Instance correct_function3_get_opcode_mem_st_reg : forall a, correct_function3 p args res f fn nil true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _op.

    unfold stateless, opcode_correct in c0.
    destruct c0 as (Hc_eq & Hc_range).
    subst.

    eexists. exists m, Events.E0.
    unfold byte_to_opcode_mem_st_reg.
    repeat split; unfold step2.
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
      unfold match_res, opcode_mem_st_reg_correct.
      rewrite Nat_land_0xff; auto.
      destruct (c =? 99) eqn: Hstxw;
      [rewrite Nat.eqb_eq in Hstxw; subst; reflexivity | rewrite Nat.eqb_neq in Hstxw].
      destruct (c =? 107) eqn: Hstxh;
      [rewrite Nat.eqb_eq in Hstxh; subst; reflexivity | rewrite Nat.eqb_neq in Hstxh].
      destruct (c =? 115) eqn: Hstxb;
      [rewrite Nat.eqb_eq in Hstxb; subst; reflexivity | rewrite Nat.eqb_neq in Hstxb].
      destruct (c =? 123) eqn: Hstxdw;
      [rewrite Nat.eqb_eq in Hstxdw; subst; reflexivity | rewrite Nat.eqb_neq in Hstxdw].

      assert (Hswitch:
          match c with
          | 99 => op_BPF_STXW
          | 107 => op_BPF_STXH
          | 115 => op_BPF_STXB
          | 123 => op_BPF_STXDW
          | _ => op_BPF_STX_ILLEGAL_INS
          end = op_BPF_STX_ILLEGAL_INS). {
          do 99 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hstxw; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hstxh; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hstxb; reflexivity | ].
          do 7 (destruct c; [reflexivity |]).
          destruct c; [exfalso; apply Hstxdw; reflexivity | reflexivity].
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
Qed.

End Get_opcode_mem_st_reg.

Close Scope nat_scope.

Existing Instance correct_function3_get_opcode_mem_st_reg.
