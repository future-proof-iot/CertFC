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

Require Import List.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.

From dx Require Import ResultMonad IR.

(* Derive Nat as unsigned int *)
(* To ensure soundness, S is not derived as +1, only O is derivable *)
(* One can still provide a primitive encoding for specific constants *)

Definition type_int_for_nat : Ctypes.type :=
  Ctypes.Tint Ctypes.I32 Ctypes.Unsigned Ctypes.noattr.

Definition zero : Csyntax.expr :=
  Csyntax.Eval Values.Vzero type_int_for_nat.

Definition one : Csyntax.expr :=
  Csyntax.Eval Values.Vone type_int_for_nat.

Definition pred (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x one type_int_for_nat.

Definition natCompilableType :=
  MkCompilableType nat type_int_for_nat.

Definition natSymbolType :=
  MkCompilableSymbolType nil (Some natCompilableType).

Definition natMatchableType :=
  MkMatchableType natCompilableType
    (fun x cases =>
      match cases with
      | [caseO;caseN] =>
        Ok (Csyntax.Sifthenelse
              (Csyntax.Ebinop Cop.Oeq x zero type_int_for_nat)
              caseO caseN)
      | _ => Err MatchEncodingFailed
      end)
    [[];[pred]]
    [[]; [natCompilableType]]
    (fun m A n whenO whenS =>
      match n with O => whenO | S n' => whenS n' end).

Definition natO := constant natSymbolType O zero.

Module Exports.
  Definition natMatchableType := natMatchableType.
  Definition natO := natO.
End Exports.
