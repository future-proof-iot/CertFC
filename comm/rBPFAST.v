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