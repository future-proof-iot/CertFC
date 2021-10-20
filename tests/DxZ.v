From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers.

(* Coq2C: Z -> signed int *)

Definition ZCompilableType :=
  MkCompilableType Z C_S64.

Open Scope Z_scope.

Definition z_0x07 := 0x07.
Definition z_0x0f := 0x0f.
Definition z_0x87 := 0x87.
Definition z_0x04 := 0x04.
Definition z_0x0c := 0x0c.
Definition z_0x84 := 0x84.
Definition z_0x95 := 0x95.

Definition z_0xff := 0xff.

Definition C_Z_0x07: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0x07)) C_S64.
Definition C_Z_0x0f: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0x0f)) C_S64.
Definition C_Z_0x87: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0x87)) C_S64.
Definition C_Z_0x04: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0x04)) C_S64.
Definition C_Z_0x0c: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0x0c)) C_S64.
Definition C_Z_0x84: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0x84)) C_S64.
Definition C_Z_0x95: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0x95)) C_S64.

Definition C_Z_0xff: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0xff)) C_S64.

Definition zSymbolType :=
  MkCompilableSymbolType nil (Some ZCompilableType).

Definition Const_Z_0x07 := constant zSymbolType z_0x07 C_Z_0x07.
Definition Const_Z_0x0f := constant zSymbolType z_0x0f C_Z_0x0f.
Definition Const_Z_0x87 := constant zSymbolType z_0x87 C_Z_0x87.
Definition Const_Z_0x04 := constant zSymbolType z_0x04 C_Z_0x04.
Definition Const_Z_0x0c := constant zSymbolType z_0x0c C_Z_0x0c.
Definition Const_Z_0x84 := constant zSymbolType z_0x84 C_Z_0x84.
Definition Const_Z_0x95 := constant zSymbolType z_0x95 C_Z_0x95.
Definition Const_Z_0xff := constant zSymbolType z_0xff C_Z_0xff.

Close Scope Z_scope.

Module Exports.
  Definition ZCompilableType := ZCompilableType.
  Definition Const_Z_0x07 := Const_Z_0x07.
  Definition Const_Z_0x0f := Const_Z_0x0f.
  Definition Const_Z_0x87 := Const_Z_0x87.
  Definition Const_Z_0x04 := Const_Z_0x04.
  Definition Const_Z_0x0c := Const_Z_0x0c.
  Definition Const_Z_0x84 := Const_Z_0x84.
  Definition Const_Z_0x95 := Const_Z_0x95.
  Definition Const_Z_0xff := Const_Z_0xff.
End Exports.
