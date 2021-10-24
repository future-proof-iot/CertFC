From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values AST.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

Require Import CoqIntegers DxIntegers.

Definition memoryChunkCompilableType :=
  MkCompilableType memory_chunk C_U32.

Definition memoryChunkSymbolType :=
  MkCompilableSymbolType nil (Some memoryChunkCompilableType).

Definition Const_Mint8unsigned := constant memoryChunkSymbolType Mint8unsigned C_U32_8.

Definition Const_Mint16unsigned := constant memoryChunkSymbolType Mint16unsigned C_U32_16.

Definition Const_Mint32 := constant memoryChunkSymbolType Mint32 C_U32_32.

Definition Const_Mint64 := constant memoryChunkSymbolType Mint64 C_U32_64.

Module Exports.
  Definition memoryChunkCompilableType := memoryChunkCompilableType.
  Definition Const_Mint8unsigned       := Const_Mint8unsigned.
  Definition Const_Mint16unsigned      := Const_Mint16unsigned.
  Definition Const_Mint32              := Const_Mint32.
  Definition Const_Mint64              := Const_Mint64.
End Exports.