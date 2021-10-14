Require Import List.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers.

Definition int64_t := Integers.int64.

(*
Definition int64_zero := Integers.Int64.zero.

Definition vall_zero: Values.val := Values.Vlong int64_zero.*)

Definition C_U64_zero: Csyntax.expr :=
  Csyntax.Eval (Values.Vlong Integers.Int64.zero) C_U64.

(*
Definition int64_one := Integers.Int64.one.

Definition vall_one: Values.val := Values.Vlong int64_one.*)

Definition C_U64_one: Csyntax.expr :=
  Csyntax.Eval (Values.Vlong Integers.Int64.one) C_U64.

Definition C_U64_add (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U64.

Definition C_U64_sub (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U64.

Definition int64CompilableType :=
  MkCompilableType int64_t C_U64.

Definition int64SymbolType :=
  MkCompilableSymbolType nil (Some int64CompilableType).

Definition Const_int64_zero := constant int64SymbolType Integers.Int64.zero C_U64_zero.

Definition Const_int64_one := constant int64SymbolType Integers.Int64.one C_U64_one.

Definition int64Toint64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType; int64CompilableType] (Some int64CompilableType).

Definition int64_add := Integers.Int64.add.

Definition Const_int64_add :=
  MkPrimitive int64Toint64Toint64SymbolType
                int64_add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition int64_sub := Integers.Int64.sub.

Definition Const_int64_sub :=
  MkPrimitive int64Toint64Toint64SymbolType
                int64_sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition int64CompilableType := int64CompilableType.
  Definition Const_int64_zero := Const_int64_zero.
  Definition Const_int64_one := Const_int64_one.
  Definition Const_int64_add := Const_int64_add.
  Definition Const_int64_sub := Const_int64_sub.
End Exports.