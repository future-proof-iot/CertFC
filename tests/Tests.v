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
From dx.Type Require Bool Nat.

Open Scope string.

Definition state := Integers.int64.

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

Module MyList1.

  Definition t := list state.
  Definition get (l: t) (idx: state): state := 
    List.nth (Z.to_nat (Integers.Int64.unsigned idx)) l (Integers.Int64.zero).

  (*Definition get (l: t) (idx: state): M state := 
    match List.nth_error l (Z.to_nat (Integers.Int64.unsigned idx)) with
    | Some res => returnM res
    | None => emptyM
    end.*)

End MyList1.

Definition MyListType := MyList1.t.
Definition MyListGet := MyList1.get.

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
  returnM (Integers.Int64.add a b).

Definition MySum (a b: state): state := Integers.Int64.add a b.

Fixpoint interpreter1 (fuel: nat) (init idx: state) (l: MyListType){struct fuel}: M unit :=
  match fuel with
  | O => emptyUnitM
  | S fuel' =>
    do i <- returnM (MyListGet l idx);
    do s <- sum init i;
      interpreter1 fuel' s (Integers.Int64.sub idx Integers.Int64.one) l
  end.

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

(** "Mapping relations from Coq to C":
  Coq:          -> C:
  l:list state  -> uint64_t *l
  get l idx     -> *(l+idx)
 *)
Definition C_U64 := Ctypes.Tlong Ctypes.Unsigned Ctypes.noattr.

Definition Cpointer := Ctypes.Tpointer C_U64 Ctypes.noattr.

Definition get_index (x idx: Csyntax.expr): Csyntax.expr :=
  Csyntax.Eindex x idx C_U64.

(** Coq2C: state -> uint64_t *)
Definition MyStateCompilableType :=
  MkCompilableType state C_U64.

(** Coq2C: l:list state  -> uint64_t *l *)
Definition MyList1CompilableType :=
  MkCompilableType MyListType Cpointer.

(** Type for MyList.t -> MyList.t *)
Definition MyListToMyListCompilableSymbolType :=
  MkCompilableSymbolType [MyList1CompilableType] (Some MyList1CompilableType).

(** Type for MyList.t -> state -> state *)
Definition MyListToStateToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyList1CompilableType; MyStateCompilableType] (Some MyStateCompilableType).

(** Type for state -> state -> state *)
Definition StateToStateToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyStateCompilableType; MyStateCompilableType] (Some MyStateCompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myList1GetPrimitive := 
  MkPrimitive MyListToStateToStateCompilableSymbolType 
              MyListGet
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** Coq2C: MySum a b -> a + b *)
Definition myList1SumPrimitive := 
  MkPrimitive StateToStateToStateCompilableSymbolType 
              MySum
              (fun es => match es with
                         | [e1; e2] => Ok (Csyntax.Ebinop Cop.Oadd e1 e2 C_U64)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(*
(** Q: Why do we need this axiom? *)
Axiom axiom : nat.
*)

Definition externEmptyUnitM := MkDerivableSymbol M "emptyUnitM" true (MkCompilableSymbolType [] None) emptyUnitM true.

Close Scope monad_scope.

(***************************************)


GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Nat.Exports
  myList1GetPrimitive
  myList1SumPrimitive
  MyStateCompilableType
  __
  externEmptyUnitM
  interpreter1.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.
