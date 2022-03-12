From bpf.comm Require Import Regs State Monad.
From bpf.monadicmodel Require Import rBPFInterpreter.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.proof Require Import Clightlogic MatchState CorrectRel CommonLemma.

From bpf.clight Require Import interpreter.

(**
Check get_src.
get_src
     : int64_t -> M reg

 *)

Open Scope Z_scope.

Section Get_src.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (reg:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_src.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_src.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv) args :=
    (dcons (fun x => StateLess (int64_correct x))
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv := fun x  => StateLess (reg_correct x).

  Instance correct_function_get_src : forall a, correct_function p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    simpl.
    unfold get_src, int64_to_src_reg.
    destruct int64_to_src_reg' eqn: Hsrc; [| constructor].
    unfold int64_to_src_reg' in Hsrc.

    get_invariant _ins.

    unfold eval_inv, int64_correct in c0.
    subst.
    unfold z_to_reg, Regs.get_src in Hsrc.
    simpl in c.
    exists (Vint (Int.repr (Int64.unsigned (Int64.shru (Int64.and c (Int64.repr 65535)) (Int64.repr 12))))), m, Events.E0.

    split_and; auto;unfold step2.
    -
      repeat forward_star.
    -
      unfold match_res.
      unfold reg_correct. (**r we need the invariant reg \in [0; 10] *)
      remember ((Int64.unsigned (Int64.shru (Int64.and c (Int64.repr 65535)) (Int64.repr 12)))) as X.
      destruct (X =? 0) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq0].

      destruct (X =? 1) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq1].

      destruct (X =? 2) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq2].

      destruct (X =? 3) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq3].

      destruct (X =? 4) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq4].

      destruct (X =? 5) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq5].

      destruct (X =? 6) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq6].

      destruct (X =? 7) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq7].

      destruct (X =? 8) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq8].

      destruct (X =? 9) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq9].

      destruct (X =? 10) eqn: Heq;
      [ rewrite Z.eqb_eq in Heq; rewrite Heq; inversion Hsrc; simpl; reflexivity |
        rewrite Z.eqb_neq in Heq; rename Heq into Heq10].

      inversion Hsrc.
    - simpl.
      constructor.
      reflexivity.
  Qed.

End Get_src.
Close Scope Z_scope.

Existing Instance correct_function_get_src.
