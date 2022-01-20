From bpf.comm Require Import rBPFAST State Monad.
From bpf.src Require Import DxValues DxInstructions.
From dx.Type Require Import Bool.
From dx Require Import IR.
From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.proof Require Import clight_exec Clightlogic CorrectRel MatchState CommonLemma.

From bpf.clight Require Import interpreter.

Section Is_well_chunk_bool.

Variable st_block : block.
Variable mrs_block: block.
Variable ins_block: block.

(** The program contains our function of interest [fn] *)
Definition p : Clight.program := prog.

(* [Args,Res] provides the mapping between the Coq and the C types *)
Definition args : list Type := [memory_chunk:Type].
Definition res : Type := bool.

(* [f] is a Coq Monadic function with the right type *)
Definition f := is_well_chunk_bool.
Locate f_is_well_chunk_bool.
(* [fn] is the Cligth function which has the same behaviour as [f] *)
Definition fn: Clight.function := f_is_well_chunk_bool.

Definition match_state (st_block : block) (_ : unit) (v : val) (st: State.state) (m : Memory.Mem.mem) : Prop :=
  v = Vptr st_block Ptrofs.zero /\ match_state st_block mrs_block ins_block st m.

Ltac exec_seq_of_labeled_statement :=
  match goal with
  | |- context[seq_of_labeled_statement ?X] =>
      let x := (eval simpl in (seq_of_labeled_statement X)) in
      change (seq_of_labeled_statement X) with x
  end.

Instance correct_function_is_well_chunk_bool2 : forall a, correct_function3
    p args res f fn nil true (DList.DCons  (stateless match_chunk) (DList.DNil _)) (stateless match_bool) a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold INV, f.
  repeat intro.
  simpl in *.
  destruct (is_well_chunk_bool c st) eqn: Heq; [idtac | constructor].
  destruct p0 as (v',st'); intros.

  get_invariant_more _chunk.
  unfold stateless, match_chunk in H0.
  subst.

  exists (Vint (if v' then Integers.Int.one else Integers.Int.zero)).
  exists m, Events.E0.
  
  repeat split; unfold step2.
  -
    unfold memory_chunk_to_valu32, well_chunk_Z in p0.
    unfold align_chunk in p0.
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
  - unfold is_well_chunk_bool, returnM in Heq.
    destruct c; inversion Heq; reflexivity.
Qed.

End Is_well_chunk_bool.

Existing Instance correct_function_is_well_chunk_bool2.
