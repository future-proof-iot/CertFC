From compcert Require Import Values Clight Memory Integers.
From Coq Require Import List ZArith.
Import ListNotations.

Fixpoint bind_parameter_temps_s
  (formals : list (AST.ident * Ctypes.type)) (args : list val)
  (le : temp_env) {struct formals} :  temp_env :=
  match formals with
  | [] => le
  | (id, _) :: xl =>
      match args with
      | [] => le
      | v :: vl => bind_parameter_temps_s xl vl (Maps.PTree.set id v le)
      end
  end.

Lemma bind_parameter_temps_eq :
  forall formals args le
         (LEN : List.length formals = List.length args),
    bind_parameter_temps formals args le =
      Some (bind_parameter_temps_s formals args le).
Proof.
  induction formals.
  - simpl. destruct args; try discriminate.
    reflexivity.
  - destruct args ; try discriminate.
    simpl.
    destruct a.
    intros.
    apply IHformals.
    congruence.
Qed.
