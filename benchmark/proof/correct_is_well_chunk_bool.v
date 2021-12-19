From bpf.src Require Import DxIntegers DxValues DxAST DxState DxMonad DxInstructions.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.proof Require Import clight_exec Clightlogic CorrectRel MatchState CommonLemma.

From bpf.benchmark Require Import clightlogicexample.


Definition match_state (st_block : block) (_ : unit) (v : val) (st: stateM) (m : Memory.Mem.mem) : Prop :=
  v = Vptr st_block Ptrofs.zero /\ match_state st_block st m.


Section Is_well_chunk_bool.
Variable st_block : block.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition Args : list Type := [memory_chunk:Type].
Definition Res : Type := bool.

(* [f] is a Coq Monadic function with the right type *)
Definition f := is_well_chunk_bool.
Locate f_is_well_chunk_bool.
(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_is_well_chunk_bool.



Ltac exec_seq_of_labeled_statement :=
  match goal with
  | |- context[seq_of_labeled_statement ?X] =>
      let x := (eval simpl in (seq_of_labeled_statement X)) in
      change (seq_of_labeled_statement X) with x
  end.

Instance correct_function_is_well_chunk_bool2 : correct_function3
    p Args Res f fn [] true (DList.DCons  (stateless match_chunk) (DList.DNil _)) (stateless match_bool).
Proof.
  correct_function_from_body.
  correct_body.
  unfold INV, f.
  repeat intro.
  simpl in *.
  destruct (is_well_chunk_bool c st) eqn: Heq; [idtac | constructor].
  destruct p0 as (v',st'); intros.

  get_invariant_more _chunk.
  unfold stateless, match_chunk in H1.
  subst.

  exists (Vint (if v' then Integers.Int.one else Integers.Int.zero)).
  exists m, Events.E0.
  repeat split; unfold step2.
  -
    unfold Int.one in *.
    destruct c; inv Heq; simpl.
    all: try
    forward_star;
    [ forward_star  |
    rewrite Int.unsigned_repr; [idtac | rewrite Int_max_unsigned_eq64; lia];
    simpl;
    repeat forward_star | reflexivity].
  - simpl.
    constructor.
    destruct v' ; reflexivity.
Qed.

End Is_well_chunk_bool.

Existing Instance correct_function_is_well_chunk_bool2.
