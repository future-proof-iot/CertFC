Require Import List.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.

Definition int64_t := Integers.int64.

Definition C_uint64_t: Ctypes.type :=
  Ctypes.Tlong Ctypes.Unsigned Ctypes.noattr.

Definition C_U64_zero := Integers.Int64.zero.

Definition VLzero: Values.val := Values.Vlong C_U64_zero.

Definition C_uint64_zero: Csyntax.expr :=
  Csyntax.Eval VLzero C_uint64_t.


Definition C_U64_one := Integers.Int64.one.

Definition VLone: Values.val := Values.Vlong C_U64_one.

Definition C_uint64_one: Csyntax.expr :=
  Csyntax.Eval VLone C_uint64_t.

Definition C_uint64_add (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_uint64_t.

Definition C_uint64_sub (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_uint64_t.

Definition int64CompilableType :=
  MkCompilableType int64_t C_uint64_t.

Definition int64SymbolType :=
  MkCompilableSymbolType nil (Some int64CompilableType).

Definition int64_zero := constant int64SymbolType C_U64_zero C_uint64_zero.

Definition int64_one := constant int64SymbolType C_U64_one C_uint64_one.

Definition int64Toint64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType; int64CompilableType] (Some int64CompilableType).

Definition C_U64_add := Integers.Int64.add.

Definition int64Add :=
  MkPrimitive int64Toint64Toint64SymbolType
                C_U64_add
                (fun es => match es with
                           | [e1;e2] => Ok (C_uint64_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition C_U64_sub := Integers.Int64.sub.

Definition int64Sub :=
  MkPrimitive int64Toint64Toint64SymbolType
                C_U64_sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_uint64_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition int64CompilableType := int64CompilableType.
  Definition int64_zero := int64_zero.
  Definition int64_one := int64_one.
  Definition int64Add := int64Add.
  Definition int64Sub := int64Sub.
End Exports.