From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Errors Values.
From compcert.lib Require Integers.


From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
From dx.lib Require MyInt64 MyList.

Open Scope string.

Definition state := MyInt64.int64_t.

Definition M (A: Type) := state -> option (A * state).

Definition runM {A: Type} (x: M A) (s: state) := x s.
Definition returnM {A: Type} (a: A) : M A := fun s => Some (a, s).
Definition emptyM {A: Type} : M A := fun s => None.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B :=
  fun s =>
    match runM x s with
    | None => None
    | Some (x', s') => runM (f x') s'
    end.

Definition get : M state := fun s => Some (s, s).
Definition put (s: state) : M unit := fun s' => Some (tt, s).

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.

Open Scope monad_scope.

Definition emptyUnitM := @emptyM unit.

Definition sum (a b: state): M state :=
  returnM (MyInt64.C_U64_add a b).

Definition testget (fuel: nat) (init idx: state) (l: MyList.MyListType): M state :=
  (* returnM (MyList.MyListGet l idx) *)
  match fuel with
  | O => do i <- returnM (MyInt64.C_U64_add init idx);
          returnM i
  | S nfuel => returnM (MyList.MyListGet l idx)
  end.

(*
Fixpoint interpreter1 (fuel: nat) (init idx: state) (l: MyList.MyListType){struct fuel}: M state :=
  match fuel with
  | O => returnM (MyInt64.C_U64_one)
  | S nfuel =>
    (*do i <- returnM (MyList.MyListGet l idx);
    do s <- returnM (MyInt64.C_U64_add init i);
    do nidx <- sum idx MyInt64.C_U64_one;*)
      interpreter1 nfuel idx (MyList.MyListGet l idx) l
  end.*)

Close Scope monad_scope.

(***************************************)


GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  MyInt64.Exports
  MyList.Exports
  __
  testget.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.
