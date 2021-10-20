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
Definition z_8    := 8.
Definition z_12   := 12.
Definition z_32   := 32.
Definition z_48   := 48.
Definition z_0xfff := 0xfff.
Definition z_0xffff := 0xffff.

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
Definition C_Z_8:  Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_8)) C_S64.
Definition C_Z_12: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_12)) C_S64.
Definition C_Z_32: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_32)) C_S64.
Definition C_Z_48: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_48)) C_S64.
Definition C_Z_0xfff: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0xfff)) C_S64.
Definition C_Z_0xffff: Csyntax.expr :=
  Csyntax.Eval (Vlong (Int64.repr z_0xffff)) C_S64.

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

Definition Const_Z_8  := constant zSymbolType z_8  C_Z_8.
Definition Const_Z_12 := constant zSymbolType z_12 C_Z_12.
Definition Const_Z_32 := constant zSymbolType z_32 C_Z_32.
Definition Const_Z_48 := constant zSymbolType z_48 C_Z_48.
Definition Const_Z_0xfff := constant zSymbolType z_0xfff C_Z_0xfff.
Definition Const_Z_0xffff := constant zSymbolType z_0xffff C_Z_0xffff.

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
  Definition Const_Z_8    := Const_Z_8.
  Definition Const_Z_12   := Const_Z_12.
  Definition Const_Z_32   := Const_Z_32.
  Definition Const_Z_48   := Const_Z_48.
  Definition Const_Z_0xfff := Const_Z_0xfff.
  Definition Const_Z_0xffff := Const_Z_0xffff.
End Exports.
