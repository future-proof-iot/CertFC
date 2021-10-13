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

From Coq Require Import List.
From compcert.common Require Errors.

Declare Scope result_monad_scope.

(* Conversion should fail when we try, for instance, to store tt in a variable
   (since it is supposed to be converted into void) *)

Inductive Error : Type :=
| MatchEncodingFailed : Error
| PrimitiveEncodingFailed : Error
| StoreVoid : Error
| ZipMismatchedSizes : Error
| GlobalFunctionsNotImplemented : Error
| InitialisedGlobalConstantCannotBeConverted : Error
| CompCert : Errors.errmsg -> Error
.

Inductive Result (A: Type) : Type :=
| Ok: A -> Result A
| Err: Error -> Result A
.

Arguments Ok [A] _.
Arguments Err [A] _.

Definition bind (A B: Type) (x: Result A) (f: A -> Result B) : Result B :=
  match x with
  | Ok y  => f y
  | Err e => Err e
  end.

Arguments bind [A] [B] _ _.

Notation "'do' X <- A ; B" := (@bind _ _ A (fun X => B))
 (at level 200, X name, A at level 100, B at level 200)
 : result_monad_scope.
