From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers Int16 DxZ.

(******************** UInt16 *******************)

Definition uint16_t := int16.

Definition C_U16_zero: Csyntax.expr :=
  Csyntax.Eval (Vint Int.zero) C_U16.

Definition C_U16_one: Csyntax.expr :=
  Csyntax.Eval (Vint Int.one) C_U16.

Definition C_U16_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U16.

Definition C_U16_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U16.

Definition uint16CompilableType :=
  MkCompilableType uint16_t C_U16.

Definition uint16SymbolType :=
  MkCompilableSymbolType nil (Some uint16CompilableType).

Definition Const_uint16_zero := constant uint16SymbolType Int16.zero C_U16_zero.

Definition Const_uint16_one := constant uint16SymbolType Int16.one C_U16_one.

Definition uint16Touint16Touint16SymbolType :=
  MkCompilableSymbolType [uint16CompilableType; uint16CompilableType] (Some uint16CompilableType).

Definition Const_uint16_add :=
  MkPrimitive uint16Touint16Touint16SymbolType
                Int16.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U16_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_uint16_sub :=
  MkPrimitive uint16Touint16Touint16SymbolType
                Int16.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U16_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).


(******************** SInt16 *******************)

Definition sint16_t := int16.

Definition C_S16_zero: Csyntax.expr :=
  Csyntax.Eval (Vint Int.zero) C_S16.

Definition C_S16_one: Csyntax.expr :=
  Csyntax.Eval (Vint Int.one) C_S16.

Definition C_S16_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_S16.

Definition C_S16_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_S16.

Definition sint16CompilableType :=
  MkCompilableType sint16_t C_S16.

Definition sint16SymbolType :=
  MkCompilableSymbolType nil (Some sint16CompilableType).

Definition Const_sint16_zero := constant sint16SymbolType Int16.zero C_S16_zero.

Definition Const_sint16_one := constant sint16SymbolType Int16.one C_S16_one.

Definition sint16Tosint16Tosint16SymbolType :=
  MkCompilableSymbolType [sint16CompilableType; sint16CompilableType] (Some sint16CompilableType).

Definition Const_sint16_add :=
  MkPrimitive sint16Tosint16Tosint16SymbolType
                Int16.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_S16_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_sint16_sub :=
  MkPrimitive sint16Tosint16Tosint16SymbolType
                Int16.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_S16_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Int16 Type Casting *******************)

(** Int16.signed: uint16_t -> sint16_t
  *)
(*
Definition int16_signedSymbolType :=
  MkCompilableSymbolType [sint16CompilableType] (Some ZCompilableType).

Definition Const_int64_signed :=
  MkPrimitive int64_signedSymbolType
                Int64.signed
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Int64.unsigned: uint64_t -> uint64_t (do nothing)
  *)

Definition int64_unsignedSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some ZCompilableType).

Definition Const_int64_unsigned :=
  MkPrimitive int64_unsignedSymbolType
                Int64.unsigned
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).
*)
(** TODO: ZCompilableType is S64 while here is type casting U64 -> S64??? *)

(** Int16.repr: sint64_t -> uint16_t
  *)

Definition int16_reprSymbolType :=
  MkCompilableSymbolType [ZCompilableType] (Some sint16CompilableType).

Definition Const_int16_repr :=
  MkPrimitive int16_reprSymbolType
                Int16.repr
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** UInt32 *******************)

Definition uint32_t := int.

Definition int32_2  := Int.repr 2.
Definition int32_3  := Int.repr 3.
Definition int32_4  := Int.repr 4.
Definition int32_5  := Int.repr 5.
Definition int32_6  := Int.repr 6.
Definition int32_7  := Int.repr 7.
Definition int32_8  := Int.repr 8.
Definition int32_9  := Int.repr 9.
Definition int32_10 := Int.repr 10.

Definition int32_32 := Int.repr 32.

Definition C_U32_zero: Csyntax.expr :=
  Csyntax.Eval (Vint Int.zero) C_U32.

Definition C_U32_one: Csyntax.expr :=
  Csyntax.Eval (Vint Int.one) C_U32.

Definition C_U32_2: Csyntax.expr :=
  Csyntax.Eval (Vint int32_2) C_U32.

Definition C_U32_3: Csyntax.expr :=
  Csyntax.Eval (Vint int32_3) C_U32.

Definition C_U32_4: Csyntax.expr :=
  Csyntax.Eval (Vint int32_4) C_U32.

Definition C_U32_5: Csyntax.expr :=
  Csyntax.Eval (Vint int32_5) C_U32.

Definition C_U32_6: Csyntax.expr :=
  Csyntax.Eval (Vint int32_6) C_U32.

Definition C_U32_7: Csyntax.expr :=
  Csyntax.Eval (Vint int32_7) C_U32.

Definition C_U32_8: Csyntax.expr :=
  Csyntax.Eval (Vint int32_8) C_U32.

Definition C_U32_9: Csyntax.expr :=
  Csyntax.Eval (Vint int32_9) C_U32.

Definition C_U32_10: Csyntax.expr :=
  Csyntax.Eval (Vint int32_10) C_U32.

Definition C_U32_32: Csyntax.expr :=
  Csyntax.Eval (Vint int32_32) C_U32.

Definition C_U32_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_U32.

Definition C_U32_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U32.

Definition C_U32_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U32.

Definition uint32CompilableType :=
  MkCompilableType uint32_t C_U32.

Definition uint32SymbolType :=
  MkCompilableSymbolType nil (Some uint32CompilableType).

Definition Const_uint32_zero := constant uint32SymbolType Int.zero C_U32_zero.

Definition Const_uint32_one := constant uint32SymbolType Int.one C_U32_one.

Definition Const_uint32_2 := constant uint32SymbolType int32_2 C_U32_2.

Definition Const_uint32_3 := constant uint32SymbolType int32_3 C_U32_3.

Definition Const_uint32_4 := constant uint32SymbolType int32_4 C_U32_4.

Definition Const_uint32_5 := constant uint32SymbolType int32_5 C_U32_5.

Definition Const_uint32_6 := constant uint32SymbolType int32_6 C_U32_6.

Definition Const_uint32_7 := constant uint32SymbolType int32_7 C_U32_7.

Definition Const_uint32_8 := constant uint32SymbolType int32_8 C_U32_8.

Definition Const_uint32_9 := constant uint32SymbolType int32_9 C_U32_9.

Definition Const_uint32_10 := constant uint32SymbolType int32_10 C_U32_10.

Definition uint32Touint32SymbolType :=
  MkCompilableSymbolType [uint32CompilableType] (Some uint32CompilableType).

Definition Const_uint32_neg :=
  MkPrimitive uint32Touint32SymbolType
                Int.neg
                (fun es => match es with
                           | [e1] => Ok (C_U32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition uint32Touint32Touint32SymbolType :=
  MkCompilableSymbolType [uint32CompilableType; uint32CompilableType] (Some uint32CompilableType).

Definition Const_uint32_add :=
  MkPrimitive uint32Touint32Touint32SymbolType
                Int.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U32_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_uint32_sub :=
  MkPrimitive uint32Touint32Touint32SymbolType
                Int.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U32_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** SInt32 *******************)
Definition sint32_t := int. (**r here we should define two types for C: sint32_t and uint32_t, then we should use those two types to define rbpf functions *)

Definition C_S32_zero: Csyntax.expr :=
  Csyntax.Eval (Vint Int.zero) C_S32.

Definition C_S32_one: Csyntax.expr :=
  Csyntax.Eval (Vint Int.one) C_S32.

Definition C_S32_2: Csyntax.expr :=
  Csyntax.Eval (Vint int32_2) C_S32.

Definition C_S32_3: Csyntax.expr :=
  Csyntax.Eval (Vint int32_3) C_S32.

Definition C_S32_4: Csyntax.expr :=
  Csyntax.Eval (Vint int32_4) C_S32.

Definition C_S32_5: Csyntax.expr :=
  Csyntax.Eval (Vint int32_5) C_S32.

Definition C_S32_6: Csyntax.expr :=
  Csyntax.Eval (Vint int32_6) C_S32.

Definition C_S32_7: Csyntax.expr :=
  Csyntax.Eval (Vint int32_7) C_S32.

Definition C_S32_8: Csyntax.expr :=
  Csyntax.Eval (Vint int32_8) C_S32.

Definition C_S32_9: Csyntax.expr :=
  Csyntax.Eval (Vint int32_9) C_S32.

Definition C_S32_10: Csyntax.expr :=
  Csyntax.Eval (Vint int32_10) C_S32.

Definition C_S32_32: Csyntax.expr :=
  Csyntax.Eval (Vint int32_32) C_S32.

Definition C_S32_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_S32.

Definition C_S32_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_S32.

Definition C_S32_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_S32.

Definition sint32CompilableType :=
  MkCompilableType sint32_t C_S32.

Definition sint32SymbolType :=
  MkCompilableSymbolType nil (Some sint32CompilableType).

Definition Const_sint32_zero := constant sint32SymbolType Int.zero C_S32_zero.

Definition Const_sint32_one := constant sint32SymbolType Int.one C_S32_one.

Definition Const_sint32_2 := constant sint32SymbolType int32_2 C_S32_2.

Definition Const_sint32_3 := constant sint32SymbolType int32_3 C_S32_3.

Definition Const_sint32_4 := constant sint32SymbolType int32_4 C_S32_4.

Definition Const_sint32_5 := constant sint32SymbolType int32_5 C_S32_5.

Definition Const_sint32_6 := constant sint32SymbolType int32_6 C_S32_6.

Definition Const_sint32_7 := constant sint32SymbolType int32_7 C_S32_7.

Definition Const_sint32_8 := constant sint32SymbolType int32_8 C_S32_8.

Definition Const_sint32_9 := constant sint32SymbolType int32_9 C_S32_9.

Definition Const_sint32_10 := constant sint32SymbolType int32_10 C_S32_10.

Definition sint32Tosint32SymbolType :=
  MkCompilableSymbolType [sint32CompilableType] (Some sint32CompilableType).

Definition Const_sint32_neg :=
  MkPrimitive sint32Tosint32SymbolType
                Int.neg
                (fun es => match es with
                           | [e1] => Ok (C_S32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition sint32Tosint32Tosint32SymbolType :=
  MkCompilableSymbolType [sint32CompilableType; sint32CompilableType] (Some sint32CompilableType).

Definition Const_sint32_add :=
  MkPrimitive sint32Tosint32Tosint32SymbolType
                Int.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_S32_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_sint32_sub :=
  MkPrimitive sint32Tosint32Tosint32SymbolType
                Int.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_S32_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Int16.repr: sint64_t -> uint16_t
  *)

Definition int32_reprSymbolType :=
  MkCompilableSymbolType [ZCompilableType] (Some sint32CompilableType).

Definition Const_int_repr :=
  MkPrimitive int32_reprSymbolType
                Int.repr
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Int64 *******************)

Definition int64_t := int64.

Definition int64_2 := Int64.repr 2.

Definition int64_64 := Int64.repr 64.

Definition C_U64_zero: Csyntax.expr :=
  Csyntax.Eval (Vlong Int64.zero) C_U64.

Definition C_U64_one: Csyntax.expr :=
  Csyntax.Eval (Vlong Int64.one) C_U64.

Definition C_U64_2: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_2) C_U64.

Definition C_U64_64: Csyntax.expr :=
  Csyntax.Eval (Vlong int64_64) C_U64.

Definition int64CompilableType :=
  MkCompilableType int64_t C_U64.

Definition int64SymbolType :=
  MkCompilableSymbolType nil (Some int64CompilableType).

Definition Const_int64_zero := constant int64SymbolType Int64.zero C_U64_zero.

Definition Const_int64_one := constant int64SymbolType Int64.one C_U64_one.

Definition Const_int64_2 := constant int64SymbolType int64_2 C_U64_2.

Definition Const_int64_64 := constant int64SymbolType int64_64 C_U64_64.

Definition int64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some int64CompilableType).

Definition Const_int64_neg :=
  MkPrimitive int64Toint64SymbolType
                Int64.neg
                (fun es => match es with
                           | [e1] => Ok (C_U64_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition int64Toint64Toint64SymbolType :=
  MkCompilableSymbolType [int64CompilableType; int64CompilableType] (Some int64CompilableType).

Definition Const_int64_add :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_sub :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_and :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.and
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_and e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_shr :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.shr
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_shr (Csyntax.Ecast  e1 C_S64) e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_shru :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.shru
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_shr e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_int64_shl :=
  MkPrimitive int64Toint64Toint64SymbolType
                Int64.shl
                (fun es => match es with
                           | [e1;e2] => Ok (C_U64_shl e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).


(******************** Int64 Type Casting *******************)

(** Int64.signed: uint64_t -> sint64_t
  *)

Definition int64_signedSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some ZCompilableType).

Definition Const_int64_signed :=
  MkPrimitive int64_signedSymbolType
                Int64.signed
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Int64.unsigned: uint64_t -> uint64_t (do nothing)
  *)

Definition int64_unsignedSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some ZCompilableType).

Definition Const_int64_unsigned :=
  MkPrimitive int64_unsignedSymbolType
                Int64.unsigned
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** TODO: ZCompilableType is S64 while here is type casting U64 -> S64??? *)

(** Int64.repr: sint64_t -> uint64_t
  *)

Definition int64_reprSymbolType :=
  MkCompilableSymbolType [ZCompilableType] (Some int64CompilableType).

Definition Const_int64_repr :=
  MkPrimitive int64_reprSymbolType
                Int64.repr
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition uint16CompilableType := uint16CompilableType.
  Definition Const_uint16_zero := Const_uint16_zero.
  Definition Const_uint16_one := Const_uint16_one.
  Definition Const_uint16_add := Const_uint16_add.
  Definition Const_uint16_sub := Const_uint16_sub.
  Definition sint16CompilableType := sint16CompilableType.
  Definition Const_sint16_zero := Const_sint16_zero.
  Definition Const_sint16_one := Const_sint16_one.
  Definition Const_sint16_add := Const_sint16_add.
  Definition Const_sint16_sub := Const_sint16_sub.
  Definition Const_int16_repr := Const_int16_repr.
  Definition uint32CompilableType := uint32CompilableType.
  Definition Const_uint32_zero := Const_uint32_zero.
  Definition Const_uint32_one := Const_uint32_one.
  Definition Const_uint32_2 := Const_uint32_2.
  Definition Const_uint32_3 := Const_uint32_3.
  Definition Const_uint32_4 := Const_uint32_4.
  Definition Const_uint32_5 := Const_uint32_5.
  Definition Const_uint32_6 := Const_uint32_6.
  Definition Const_uint32_7 := Const_uint32_7.
  Definition Const_uint32_8 := Const_uint32_8.
  Definition Const_uint32_9 := Const_uint32_9.
  Definition Const_uint32_10 := Const_uint32_10.
  Definition Const_uint32_neg := Const_uint32_neg.
  Definition Const_uint32_add := Const_uint32_add.
  Definition Const_uint32_sub := Const_uint32_sub.
  Definition sint32CompilableType := sint32CompilableType.
  Definition Const_sint32_zero := Const_sint32_zero.
  Definition Const_sint32_one := Const_sint32_one.
  Definition Const_sint32_2 := Const_sint32_2.
  Definition Const_sint32_3 := Const_sint32_3.
  Definition Const_sint32_4 := Const_sint32_4.
  Definition Const_sint32_5 := Const_sint32_5.
  Definition Const_sint32_6 := Const_sint32_6.
  Definition Const_sint32_7 := Const_sint32_7.
  Definition Const_sint32_8 := Const_sint32_8.
  Definition Const_sint32_9 := Const_sint32_9.
  Definition Const_sint32_10 := Const_sint32_10.
  Definition Const_sint32_neg := Const_sint32_neg.
  Definition Const_sint32_add := Const_sint32_add.
  Definition Const_sint32_sub := Const_sint32_sub.
  Definition Const_int_repr   := Const_int_repr.
  Definition int64CompilableType := int64CompilableType.
  Definition Const_int64_zero := Const_int64_zero.
  Definition Const_int64_one := Const_int64_one.
  Definition Const_int64_2 := Const_int64_2.
  Definition Const_int64_64 := Const_int64_64.
  Definition Const_int64_neg := Const_int64_neg.
  Definition Const_int64_add := Const_int64_add.
  Definition Const_int64_sub := Const_int64_sub.
  Definition Const_int64_and := Const_int64_and.
  Definition Const_int64_signed := Const_int64_signed.
  Definition Const_int64_unsigned := Const_int64_unsigned.
  Definition Const_int64_repr := Const_int64_repr.
  Definition Const_int64_shr := Const_int64_shr.
  Definition Const_int64_shru := Const_int64_shru.
  Definition Const_int64_shl := Const_int64_shl.
End Exports.