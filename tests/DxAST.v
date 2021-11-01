From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values AST Memdata.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

Require Import CoqIntegers DxIntegers DxValues GenMatchable.

Definition memory_chunk_to_val64 (chunk: memory_chunk) := 
  Vlong (Int64.repr (size_chunk chunk)).

Definition memory_chunk_to_val64_upbound (chunk: memory_chunk) :=
  Vlong (Int64.repr (Int64.max_unsigned-(size_chunk chunk))).

(******************** Dx Related *******************)

Definition memoryChunkCompilableType :=
  MkCompilableType memory_chunk C_U32.

Definition memorychunk_eqb (o o' : memory_chunk) : bool :=
  match o , o' with
  | Mint8unsigned, Mint8unsigned
  | Mint16unsigned, Mint16unsigned
  | Mint32, Mint32
  | Mint64, Mint64 => true
  | _, _ => false
  end.

Open Scope Z_scope.
Definition memoryChunkMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    memoryChunkCompilableType  memorychunk_eqb
    ((Mint8unsigned, 8)
       :: (Mint16unsigned, 16)
       :: (Mint32, 32)
       :: (Mint64, 64)
       :: (Mint8signed, 8)
       :: (Mint16signed, 16)
       :: (Mfloat32, 32)
       :: (Mfloat64, 64)
       :: (Many32, 32) :: nil) Many64 (fun m A
=> memory_chunk_rect (fun _ => m A))).

Definition memoryChunkSymbolType :=
  MkCompilableSymbolType nil (Some memoryChunkCompilableType).

Definition Const_Mint8unsigned := constant memoryChunkSymbolType Mint8unsigned C_U32_one.

Definition Const_Mint16unsigned := constant memoryChunkSymbolType Mint16unsigned C_U32_2.

Definition Const_Mint32 := constant memoryChunkSymbolType Mint32 C_U32_4.

Definition Const_Mint64 := constant memoryChunkSymbolType Mint64 C_U32_8.

Definition memoryChunkToval64SymbolType :=
  MkCompilableSymbolType [memoryChunkCompilableType] (Some val64CompilableType).

Definition Const_memory_chunk_to_val64 :=
  MkPrimitive memoryChunkToval64SymbolType
                memory_chunk_to_val64
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_memory_chunk_to_val64_upbound :=
  MkPrimitive memoryChunkToval64SymbolType
                memory_chunk_to_val64_upbound
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ebinop Cop.Osub C_U64_max_unsigned e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition memoryChunkMatchableType  := memoryChunkMatchableType.
  Definition Const_Mint8unsigned       := Const_Mint8unsigned.
  Definition Const_Mint16unsigned      := Const_Mint16unsigned.
  Definition Const_Mint32              := Const_Mint32.
  Definition Const_Mint64              := Const_Mint64.
  Definition Const_memory_chunk_to_val64:= Const_memory_chunk_to_val64.
  Definition Const_memory_chunk_to_val64_upbound := Const_memory_chunk_to_val64_upbound.
End Exports.