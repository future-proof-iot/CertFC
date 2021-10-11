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
From dx.Type Require Bool Nat MyInt64.

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


Definition testincr (a: state): M state := 
  returnM (MyInt64.C_U64_add a MyInt64.C_U64_one).

(*
Definition testincr (a: Integers.int64): M Integers.int64 := 
  returnM (Integers.Int64.add a Integers.Int64.one).*)

Close Scope monad_scope.

(***************************************)

GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  MyInt64.Exports
  __
  testincr.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.
