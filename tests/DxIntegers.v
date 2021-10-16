From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers Int16.

(******************** Int16 *******************)

Definition int16_t := Int16.int16.

Definition C_U16_zero: Csyntax.expr :=
  Csyntax.Eval (Values.Vint Integers.Int.zero) C_U16.

Definition C_U16_one: Csyntax.expr :=
  Csyntax.Eval (Values.Vint Integers.Int.one) C_U16.

Definition C_U16_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U16.

Definition C_U16_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U16.

Definition int16CompilableType :=
  MkCompilableType int16_t C_U16.

Definition int16SymbolType :=
  MkCompilableSymbolType nil (Some int16CompilableType).

Definition Const_int16_zero := constant int16SymbolType Int16.Int16.zero C_U16_zero.

Definition Const_int16_one := constant int16SymbolType Int16.Int16.one C_U16_one.

Definition int16Toint16Toint16SymbolType :=
  MkCompilableSymbolType [int16CompilableType; int16CompilableType] (Some int16CompilableType).

Definition Const_int16_add :=
  MkPrimitive int16Toint16Toint16SymbolType
                Int16.Int16.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U16_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int16_sub :=
  MkPrimitive int16Toint16Toint16SymbolType
                Int16.Int16.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U16_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Int32 *******************)

Definition int32_t := Integers.int.

Definition int32_two   := Integers.Int.repr 2.
Definition int32_three := Integers.Int.repr 3.
Definition int32_four  := Integers.Int.repr 4.
Definition int32_five  := Integers.Int.repr 5.
Definition int32_six   := Integers.Int.repr 6.
Definition int32_seven := Integers.Int.repr 7.
Definition int32_eight := Integers.Int.repr 8.
Definition int32_nine  := Integers.Int.repr 9.
Definition int32_ten   := Integers.Int.repr 10.

Definition C_U32_zero: Csyntax.expr :=
  Csyntax.Eval (Values.Vint Integers.Int.zero) C_U32.

Definition C_U32_one: Csyntax.expr :=
  Csyntax.Eval (Values.Vint Integers.Int.one) C_U32.

Definition C_U32_two: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_two) C_U32.

Definition C_U32_three: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_three) C_U32.

Definition C_U32_four: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_four) C_U32.

Definition C_U32_five: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_five) C_U32.

Definition C_U32_six: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_six) C_U32.

Definition C_U32_seven: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_seven) C_U32.

Definition C_U32_eight: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_eight) C_U32.

Definition C_U32_nine: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_nine) C_U32.

Definition C_U32_ten: Csyntax.expr :=
  Csyntax.Eval (Values.Vint int32_ten) C_U32.

Definition C_U32_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_U32.

Definition C_U32_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U32.

Definition C_U32_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U32.

Definition int32CompilableType :=
  MkCompilableType int32_t C_U32.

Definition int32SymbolType :=
  MkCompilableSymbolType nil (Some int32CompilableType).

Definition Const_int32_zero := constant int32SymbolType Integers.Int.zero C_U32_zero.

Definition Const_int32_one := constant int32SymbolType Integers.Int.one C_U32_one.

Definition Const_int32_two := constant int32SymbolType int32_two C_U32_two.

Definition Const_int32_three := constant int32SymbolType int32_three C_U32_three.

Definition Const_int32_four := constant int32SymbolType int32_four C_U32_four.

Definition Const_int32_five := constant int32SymbolType int32_five C_U32_five.

Definition Const_int32_six := constant int32SymbolType int32_six C_U32_six.

Definition Const_int32_seven := constant int32SymbolType int32_seven C_U32_seven.

Definition Const_int32_eight := constant int32SymbolType int32_eight C_U32_eight.

Definition Const_int32_nine := constant int32SymbolType int32_nine C_U32_nine.

Definition Const_int32_ten := constant int32SymbolType int32_ten C_U32_ten.

Definition int32Toint32SymbolType :=
  MkCompilableSymbolType [int32CompilableType] (Some int32CompilableType).

Definition Const_int32_neg :=
  MkPrimitive int32Toint32SymbolType
                Integers.Int.neg
                (fun es => match es with
                           | [e1] => Ok (C_U32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition int32Toint32Toint32SymbolType :=
  MkCompilableSymbolType [int32CompilableType; int32CompilableType] (Some int32CompilableType).

Definition Const_int32_add :=
  MkPrimitive int32Toint32Toint32SymbolType
                Integers.Int.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U32_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int32_sub :=
  MkPrimitive int32Toint32Toint32SymbolType
                Integers.Int.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U32_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).
(******************** Int64 *******************)

Definition int64_t := Integers.int64.

Definition int64_two := Integers.Int64.repr 2.

Definition C_U64_zero: Csyntax.expr :=
  Csyntax.Eval (Values.Vlong Integers.Int64.zero) C_U64.

Definition C_U64_one: Csyntax.expr :=
  Csyntax.Eval (Values.Vlong Integers.Int64.one) C_U64.

Definition C_U64_two: Csyntax.expr :=
  Csyntax.Eval (Values.Vlong int64_two) C_U64.

Definition C_U64_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_U64.

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

Definition Const_int64_two := constant int64SymbolType int64_two C_U64_two.

Definition int64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some int64CompilableType).

Definition Const_int64_neg :=
  MkPrimitive int64Toint64SymbolType
                Integers.Int64.neg
                (fun es => match es with
                           | [e1] => Ok (C_U64_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition int64Toint64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType; int64CompilableType] (Some int64CompilableType).

Definition Const_int64_add :=
  MkPrimitive int64Toint64Toint64SymbolType
                Integers.Int64.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_sub :=
  MkPrimitive int64Toint64Toint64SymbolType
                Integers.Int64.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition int16CompilableType := int16CompilableType.
  Definition Const_int16_zero := Const_int16_zero.
  Definition Const_int16_one := Const_int16_one.
  Definition Const_int16_add := Const_int16_add.
  Definition Const_int16_sub := Const_int16_sub.
  Definition int32CompilableType := int32CompilableType.
  Definition Const_int32_zero := Const_int32_zero.
  Definition Const_int32_one := Const_int32_one.
  Definition Const_int32_two := Const_int32_two.
  Definition Const_int32_three := Const_int32_three.
  Definition Const_int32_four := Const_int32_four.
  Definition Const_int32_five := Const_int32_five.
  Definition Const_int32_six := Const_int32_six.
  Definition Const_int32_seven := Const_int32_seven.
  Definition Const_int32_eight := Const_int32_eight.
  Definition Const_int32_nine := Const_int32_nine.
  Definition Const_int32_ten := Const_int32_ten.
  Definition Const_int32_neg := Const_int32_neg.
  Definition Const_int32_add := Const_int32_add.
  Definition Const_int32_sub := Const_int32_sub.
  Definition int64CompilableType := int64CompilableType.
  Definition Const_int64_zero := Const_int64_zero.
  Definition Const_int64_one := Const_int64_one.
  Definition Const_int64_two := Const_int64_two.
  Definition Const_int64_neg := Const_int64_neg.
  Definition Const_int64_add := Const_int64_add.
  Definition Const_int64_sub := Const_int64_sub.
End Exports.