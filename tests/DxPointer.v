From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

Require Import CoqIntegers DxIntegers.

Definition ptr_int64 := int64_t.

Definition pointerCompilableType :=
  MkCompilableType ptr_int64 C_U64_pointer.

Module Exports.
  Definition pointerCompilableType := pointerCompilableType.
End Exports.