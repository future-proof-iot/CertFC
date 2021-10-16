From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers DxIntegers.

(** Coq2C: Values.val -> unsigned long long or unsigned int
  *)

Definition val_t := Values.val.

(******************** Val2U32 *******************)

Definition val32CompilableType :=
  MkCompilableType val_t C_U32.

(** Type signature: val -> val
  *)
Definition val32Toval32SymbolType :=
  MkCompilableSymbolType [val32CompilableType] (Some val32CompilableType).

Definition Const_val32_neg :=
  MkPrimitive val32Toval32SymbolType
                Values.Val.neg
                (fun es => match es with
                           | [e1] => Ok (C_U32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: val -> val -> val
  *)
Definition val32Toval32Toval32SymbolType :=
  MkCompilableSymbolType [val32CompilableType; val32CompilableType] (Some val32CompilableType).

Definition Const_val32_add :=
  MkPrimitive val32Toval32Toval32SymbolType
                Values.Val.add
                (fun es => match es with
                           | [e1; e2] => Ok (C_U32_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Val2U64 *******************)

Definition val64CompilableType :=
  MkCompilableType val_t C_U64.

(** Type signature: val -> val
  *)
Definition val64Toval64SymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some val64CompilableType).

Definition Const_val64_neg :=
  MkPrimitive val64Toval64SymbolType
                Values.Val.negl
                (fun es => match es with
                           | [e1] => Ok (C_U64_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: val -> val -> val
  *)
Definition val64Toval64Toval64SymbolType :=
  MkCompilableSymbolType [val64CompilableType; val64CompilableType] (Some val64CompilableType).

Definition Const_val64_add :=
  MkPrimitive val64Toval64Toval64SymbolType
                Values.Val.addl
                (fun es => match es with
                           | [e1; e2] => Ok (C_U64_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition val32CompilableType := val32CompilableType.
  Definition Const_val32_neg := Const_val32_neg.
  Definition Const_val32_add := Const_val32_add.
  Definition val64CompilableType := val64CompilableType.
  Definition Const_val64_neg := Const_val64_neg.
  Definition Const_val64_add := Const_val64_add.
End Exports.
