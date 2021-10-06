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
From compcert.common Require Errors.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat MyList.

Open Scope string.

Definition state := nat.

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

Definition ready : M bool :=
  do s <- get ;
     returnM (even s).

Definition getReady : M unit :=
  do s <- get ;
     if even s
     then returnM tt
     else do _ <- put (S s) ;
             returnM tt.

Definition id (b : bool) : M bool := returnM b.

Definition neg (b : bool) : M bool := if b then returnM false else returnM true.

Definition emptyUnitM := @emptyM unit.

Fixpoint prepare recBound : M unit :=
  match recBound with
  | O   => emptyUnitM
  | S b => do r <- ready ;
              if r
              then returnM tt
              else do _ <- getReady ;
                      prepare b
  end.

Module ModTest.
Definition testId (b : bool) : M bool := returnM b.
End ModTest.

Definition boolToBoolType := MkCompilableSymbolType [Bool.boolCompilableType] (Some Bool.boolCompilableType).
Definition derivableId := MkDerivableSymbol M "id" true boolToBoolType id false.

Definition externEmptyUnitM := MkDerivableSymbol M "emptyUnitM" true (MkCompilableSymbolType [] None) emptyUnitM true.
Definition externReady := MkDerivableSymbol M "ready" true Bool.boolSymbolType ready true.
Definition externGetReady := MkDerivableSymbol M "getReady" true (MkCompilableSymbolType [] None) getReady true.

Definition derivableNeg := MkDerivableSymbol M "neg" true boolToBoolType neg false.

Axiom axiom : nat.

Close Scope monad_scope.

(***************************************)

(*

GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  derivableId
  axiom
  __
  neg
  ModTest
  externEmptyUnitM
  externReady
  externGetReady
  prepare.
*)

Definition State := nat.

Definition Error := string.
Definition M1 (A: Type) := State -> (State*A) + Error.
Definition returnM1 {A: Type} (a: A) : M1 A := fun s => inl (s, a).
Definition runM1 {A: Type} (x: M1 A) (s: state) := x s.
Definition bindM1 {A B: Type} (x: M1 A) (f: A -> M1 B) : M1 B :=
  fun s =>
    match (runM1 x s) with
    | inl s => runM1 (f (snd s)) (fst s)
    | inr e => inr e
    end.

Declare Scope monad_scope.
Notation "'do1' x <- a ; b" :=
  (bindM1 a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.

Open Scope monad_scope.

Definition returnZero: M1 nat := returnM1 0%nat.
Definition returnN (n:nat): M1 nat := returnM1 n.

Fixpoint interpreter (fuel: nat) (l: list Integers.int64): M1 nat :=
  match fuel with
  | O => returnZero
  | S n => match l with
          | nil => returnN n
          | hd :: tl => do1 res <- interpreter n tl; returnN res
          end
  end.

Close Scope monad_scope.

GenerateIntermediateRepresentation SymbolIRs
  M1 bindM1 returnM1
  Bool.Exports
  Nat.Exports
  MyList.Exports
  
  __
  interpreter.

(*
Cannot convert, skipping: MyList.Exports.listCompilableType [dx.inconvertible,dx]
Cannot convert, skipping: MyList.Exports.list_null [dx.inconvertible,dx]
Cannot convert, skipping: interpreter [dx.inconvertible,dx]
 *)
(**
int interpreter (int fuel, int *p){ //int64
  printf("fuel = %d, p = %d\n", fuel, *p);
  int res;
  if (fuel == 0){
    return 0;
  }
  else {
    p++;
    res = interpreter((fuel-1), p) + 1;
    return res;
  }
}
 *)

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.
