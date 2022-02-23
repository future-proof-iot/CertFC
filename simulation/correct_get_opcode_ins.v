From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import Opcode rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma CommonLemmaNat.

From bpf.clight Require Import interpreter.

(**
Check get_opcode_ins.
get_opcode_ins
     : int64 -> M nat

*)

Section Get_opcode_ins.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (nat:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_opcode_ins.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_ins.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args :=
    (DList.DCons (stateless ins64_correct)
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop := fun x v st m => opcode_correct x v.

  Instance correct_function3_get_opcode_ins : forall a, correct_function3 p args res f fn nil true match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _ins.

    unfold stateless, ins64_correct in c0.
    destruct c0 as (Hc_eq & _).
    subst.

    eexists. exists m, Events.E0.
    unfold int64_to_opcode.
    repeat split; unfold step2.
    -
      forward_star.
      rewrite Z2Nat.id.
      simpl.
      rewrite Int.zero_ext_idem; [| lia].
      rewrite Int.zero_ext_and; [| lia].
      change (two_p 8 - 1)%Z with 255%Z.
      unfold Int.and.
      forward_star.
      rewrite Z.land_nonneg.
      right; lia.
    -
      assert (Hc_le: (0 <= Int64.unsigned (Int64.and c (Int64.repr 255)) <= 255)%Z). {
        rewrite Int64.and_commut.
        split.
        assert (Hrange: (0 <= Int64.unsigned (Int64.and (Int64.repr 255) c) < Int64.modulus)%Z) by apply Int64.unsigned_range.
        lia.
        apply Int64.and_le.
      }
      remember (Int64.unsigned (Int64.and c (Int64.repr 255))) as n.
      rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
      rewrite <- Z2Nat.id with (n:=n); [| lia].
      change 255%Z with (Z.of_nat (Z.to_nat 255%Z)).
      rewrite LemmaNat.land_land.
      rewrite Nat2Z.id.
      assert (Hc_leZ: 0 <= Z.to_nat n <= 255) by lia.
      change (Z.to_nat 255%Z) with 255.
      rewrite Nat.land_comm.
      rewrite LemmaNat.land_bound.
      lia.
    - constructor.
      simpl.
      assert (Hc_le: (0 <= Int64.unsigned (Int64.and c (Int64.repr 255)) <= 255)%Z). {
        rewrite Int64.and_commut.
        split.
        assert (Hrange: (0 <= Int64.unsigned (Int64.and (Int64.repr 255) c) < Int64.modulus)%Z) by apply Int64.unsigned_range.
        lia.
        apply Int64.and_le.
      }
      remember (Int64.unsigned (Int64.and c (Int64.repr 255))) as n.
      rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
      rewrite Z2Nat.id.
      + assert (Hpre: (0 <= 8 < Int.zwordsize)%Z) by (change Int.zwordsize with 32%Z; lia).
        assert (Hz_land: (0 <= Z.land n 255 <= 255)%Z). {
          split.
          rewrite Z.land_nonneg.
          right; lia.
          rewrite <- Z2Nat.id with (n:=n); [| lia].
          change 255%Z with (Z.of_nat (Z.to_nat 255%Z)) at 1.
          rewrite LemmaNat.land_land.
          assert (Hc_leZ: 0 <= Z.to_nat n <= 255) by lia.
          change (Z.to_nat 255%Z) with 255.
          rewrite Nat.land_comm.
          assert (Hc_leN: Nat.land 255 (Z.to_nat n) <= 255) by
          (rewrite LemmaNat.land_bound; lia).
          lia.
        }
        rewrite Int.zero_ext_and.
        change (two_p 8 - 1)%Z with 255%Z.
        unfold Int.and.
        change (Int.unsigned (Int.repr 255)) with 255%Z.
        rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
        rewrite <- Z.land_assoc.
        rewrite Z.land_diag.
        reflexivity.
        lia.
      + rewrite Z.land_nonneg.
        right; lia.
Qed.

End Get_opcode_ins.

Existing Instance correct_function3_get_opcode_ins.
