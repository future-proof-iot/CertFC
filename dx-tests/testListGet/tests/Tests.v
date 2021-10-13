(**************************************************************************)
(*  This file is part of dx, a tool to derive C from monadic Gallina.     *)
(*                                                                        *)
(*  Copyright (C) 2021 Université de Lille & CNRS                         *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(**************************************************************************)

From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Errors Values.
From compcert.lib Require Integers.


From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat MyInt64 MyList.

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

(*
Module MyList2.

  Definition t := list state.
  Definition get (l: t) (idx: state): M (Values.val) := 
    match List.nth_error l (Z.to_nat (Integers.Int64.unsigned idx)) with
    | Some res => returnM (Values.Vlong res)
    | None => emptyM
    end.

End MyList2.
*)

Definition emptyUnitM := @emptyM unit.

Definition sum (a b: state): M state :=
  returnM (MyInt64.C_U64_add a b).

Definition testget (fuel: nat) (init idx: state) (l: MyList.MyListType): M state :=
  returnM (MyList.MyListGet l idx).
(*
  match fuel with
  | O => returnM init
  | S fuel' => returnM (MyList.MyListGet l idx)
  end.*)

(*
Fixpoint interpreter1 (fuel: nat) (init idx: state) (l: MyList.MyListType){struct fuel}: M unit :=
  match fuel with
  | O => emptyUnitM
  | S fuel' =>
      interpreter1 fuel' (MyList.MyListGet l idx) (MyInt64.C_U64_sub idx MyInt64.C_U64_one) l
  end.
*)
(** "target C":
uint64_t interpreter1 (unsigned int fuel, uint64_t init, uint64_t idx, uint64_t *l){
  unsigned int b_i;
  uint64_t b_j, b_k, b_r;
  if (fuel == 0U) {
    emptyUnitM();
    return;
  }
  else {
    b_i = fuel - 1U;
    b_j = get(l, idx);
    b_k = sum(init, b_j);
    b_r = interpreter1 (b_i, b_k, (idx-1) l);
    return b_r;
  }
}
 *)

(*
Definition externEmptyUnitM := MkDerivableSymbol M "emptyUnitM" true (MkCompilableSymbolType [] None) emptyUnitM true.*)

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