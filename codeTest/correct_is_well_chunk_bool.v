Require Import   interpreter.
From dx.tests Require Import DxIntegers DxValues DxAST DxState DxMonad DxInstructions.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.
Require Import ZArith.

Require Import clight_exec Clightlogic StateBlock CommonLemma.


Definition match_state (st_block : block) (_ : unit) (v : val) (st: stateM) (m : Memory.Mem.mem) : Prop :=
  v = Vptr st_block Ptrofs.zero /\ match_state_block st st_block m.


Section Is_well_chunk_bool.
Variable st_block : block.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition Args : list Type := [memory_chunk:Type].
Definition Res : Type := bool.

(* [f] is a Coq Monadic function with the right type *)
Definition f := is_well_chunk_bool.

(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_is_well_chunk_bool.

Definition match_chunk (x : memory_chunk) (b: val) :=
  b = Vint (
          match x with
          | Mint8unsigned => Integers.Int.one
          | Mint16unsigned => Integers.Int.repr 2
          | Mint32 => Integers.Int.repr 4
          | Mint64 => Integers.Int.repr 8
          | _ => Integers.Int.repr 0
          end).


Ltac exec_seq_of_labeled_statement :=
  match goal with
  | |- context[seq_of_labeled_statement ?X] =>
      let x := (eval simpl in (seq_of_labeled_statement X)) in
      change (seq_of_labeled_statement X) with x
  end.




Lemma correct_function_is_well_chunk_bool2 : forall unmod,
  correct_function3
    p Args Res f fn unmod true (DList.DCons  (stateless match_chunk) (DList.DNil _)) (stateless match_bool).
Proof.
  intro.
  correct_function_from_body.
  repeat intro.
  simpl in H.
  unfold Args in a.
  car_cdr.
  unfold list_rel_arg in H.
  simpl in H.
  unfold app.
  unfold f,f_is_well_chunk_bool.
  destruct (is_well_chunk_bool c st) eqn:E ; auto.
  destruct p0 as (v',st'); intros.
  unfold fn at 2. unfold f_is_well_chunk_bool.
  unfold fn_body.
  get_invariant _chunk0.
  destruct c0 as [MC  C].
  unfold stateless in MC.
  unfold match_chunk in MC.
  subst.
  exists (Vint (if v' then Integers.Int.one else Integers.Int.zero)).
  exists m. exists Events.E0.
  repeat split.
  + eapply Smallstep.star_step; eauto.
    econstructor; eauto.
    econstructor;eauto.
    constructor.
    unfold Integers.Int.one.
    destruct c;inv E.
    Ltac switch :=
      match goal with
        |- context[Integers.Int.unsigned (Integers.Int.repr ?X)] =>
          change (Integers.Int.unsigned (Integers.Int.repr X)) with X;
          exec_seq_of_labeled_statement
      end;
      eapply Smallstep.star_step; eauto;
      [econstructor;eauto |
        eapply Smallstep.star_step; eauto ; [econstructor; eauto;
                                            econstructor; eauto|]
      ]; apply Smallstep.star_refl.
    all: try switch.
    reflexivity.
  + simpl.
    constructor.
    destruct v' ; reflexivity.
Qed.

End Is_well_chunk_bool.
