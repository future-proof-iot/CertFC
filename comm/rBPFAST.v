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
From compcert.common Require Import Values AST Memdata.
From compcert.lib Require Import Integers.

Definition well_chunk_Z (chunk: memory_chunk):Z := 
  match chunk with
  | Mint8unsigned => 1
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | _ => 10
  end.

Definition memory_chunk_to_valu32 (chunk: memory_chunk): val := 
  Vint (Int.repr (well_chunk_Z chunk)). (**r well_chunk implies align_chunk, so we didn't need align_chunk, but we must prove a lemma! *)

Definition memory_chunk_to_valu32_upbound (chunk: memory_chunk): val :=
  Vint (Int.repr (Int.max_unsigned-(well_chunk_Z chunk))).

Definition chunk_eqb (c1 c2: memory_chunk) : bool :=
  match c1, c2 with
  | Mint8signed, Mint8signed
  | Mint8unsigned, Mint8unsigned
  | Mint16signed, Mint16signed
  | Mint16unsigned, Mint16unsigned
  | Mint32, Mint32
  | Mint64, Mint64
  | Mfloat32, Mfloat32
  | Mfloat64, Mfloat64
  | Many32, Many32
  | Many64, Many64 => true
  | _, _ => false
  end.

Lemma chunk_eqb_true:
  forall x y, x = y <-> chunk_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma chunk_eqb_false:
  forall x y, x <> y <-> chunk_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Definition is_well_chunkb (chunk: memory_chunk) : bool :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 | Mint64 => true
  | _ => false
  end.

Definition is_vint_or_vlong_chunk (chunk: memory_chunk) (v: val): bool :=
  match chunk, v with
  | Mint8unsigned, Vint _
  | Mint16unsigned, Vint _
  | Mint32, Vint _
  | Mint64, Vlong _  => true
  | _, _ => false
  end.

Definition _to_vlong (v: val): option val :=
  match v with
  | Vlong n => Some (Vlong n) (**r Mint64 *)
  | Vint  n => Some (Vlong (Int64.repr (Int.unsigned n))) (**r Mint8unsigned, Mint16unsigned, Mint32 *) (* (u64) v *)
  | _       => None
  end.

Definition vlong_to_vint_or_vlong (chunk: memory_chunk) (v: val): val :=
  match v with
  | Vlong n =>
    match chunk with
    | Mint8unsigned => Vint (Int.zero_ext 8 (Int.repr (Int64.unsigned n)))
    | Mint16unsigned => Vint (Int.zero_ext 16 (Int.repr (Int64.unsigned n)))
    | Mint32 => Vint (Int.repr (Int64.unsigned n))
    | Mint64 => Vlong n
    | _      => Vundef
    end
  | _       => Vundef
  end.

Definition vint_to_vint_or_vlong (chunk: memory_chunk) (v: val): val :=
  match v with
  | Vint n =>
    match chunk with
    | Mint8unsigned => (Vint (Int.zero_ext 8 n))
    | Mint16unsigned => (Vint (Int.zero_ext 16 n))
    | Mint32 => Vint n
    | Mint64 => (Vlong (Int64.repr (Int.signed n)))
    | _      => Vundef
    end
  | _       => Vundef
  end.