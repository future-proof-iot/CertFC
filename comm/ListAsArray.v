(**************************************************************************)
(*  This file is part of CertrBPF,                                        *)
(*  a formally verified rBPF verifier + interpreter + JIT in Coq.         *)
(*                                                                        *)
(*  Copyright (C) 2022 Inria                                              *)
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
(*                                                                        *)
(**************************************************************************)

From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Import Integers.

(** This module presents a generic List as a fix-sized array in C *)

Module List64AsArray.

  Definition t := list int64.
  Definition index (l: t) (idx: int): int64 := 
    match List.nth_error l (Z.to_nat (Int.unsigned idx)) with
    | Some i => i
    | None => Int64.zero
    end.

  Fixpoint assign' (l: t) (cur: nat) (v: int64): option t :=
    match l with
    | [] => None (**r it should be impossible *)
    | hd :: tl =>
      match cur with
      | O => Some (v :: tl)
      | S n =>
        match assign' tl n v with
        | Some nl => Some (hd :: nl)
        | None => None
        end
      end
    end.

  Definition assign (l: t) (cur: nat) (v: int64): t :=
    match assign' l cur v with
    | Some nl => nl
    | None    => []
    end.

End List64AsArray.