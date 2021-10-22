From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

Require Import CoqIntegers DxIntegers InfComp.

(** Coq2C: Values.val -> unsigned long long or unsigned int
  *)

(******************** Val2U32 *******************)

Definition valu32_t := val.

Definition valU32CompilableType :=
  MkCompilableType valu32_t C_U32.

(** Type signature: val -> val
  *)
Definition valU32TovalU32SymbolType :=
  MkCompilableSymbolType [valU32CompilableType] (Some valU32CompilableType).

Definition Const_valU32_neg :=
  MkPrimitive valU32TovalU32SymbolType
                Val.neg
                (fun es => match es with
                           | [e1] => Ok (C_U32_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: val -> val -> val
  *)
Definition valU32TovalU32TovalU32SymbolType :=
  MkCompilableSymbolType [valU32CompilableType; valU32CompilableType] (Some valU32CompilableType).

Instance C_valu32 : CType valu32_t := mkCType _ (cType valU32CompilableType).

(** Type signature: val -> val -> option val
    we use `val32_divu` to replace `Val.divu`
  *)

Definition val32_divu (x y: val): val :=
  match Val.divu x y with
  | Some res => res
  | None => Vundef
  end.

(** Type signature: val -> val -> option val
    we use `val32_modu` to replace `Val.modu`
  *)

Definition val32_modu (x y: val): val :=
  match Val.modu x y with
  | Some res => res
  | None => Vundef
  end.

Definition Const_valU32_add := ltac: (mkprimitive Val.add (binop_expr Cop.Oadd C_U32)).
Definition Const_valU32_sub := ltac: (mkprimitive Val.sub (binop_expr Cop.Osub C_U32)).
Definition Const_valU32_mul := ltac: (mkprimitive Val.mul (binop_expr Cop.Omul C_U32)).
Definition Const_valU32_div := ltac: (mkprimitive val32_divu (binop_expr Cop.Odiv C_U32)).
Definition Const_valU32_or  := ltac: (mkprimitive Val.or  (binop_expr Cop.Oor  C_U32)).
Definition Const_valU32_and := ltac: (mkprimitive Val.and (binop_expr Cop.Oand C_U32)).
Definition Const_valU32_shl := ltac: (mkprimitive Val.shl (binop_expr Cop.Oshl C_U32)).
Definition Const_valU32_shr := ltac: (mkprimitive Val.shru (binop_expr Cop.Oshr C_U32)).
Definition Const_valU32_mod := ltac: (mkprimitive val32_modu (binop_expr Cop.Omod C_U32)).
Definition Const_valU32_xor := ltac: (mkprimitive Val.xor (binop_expr Cop.Oxor C_U32)).

Definition Const_valU32_shrs :=
  MkPrimitive valU32TovalU32TovalU32SymbolType
                Val.shr
                (fun es => match es with
                           | [e1; e2] => Ok (C_U32_shr (Csyntax.Ecast  e1 C_S32) e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Val2S32 *******************)

Definition vals32_t := val.

Definition valS32CompilableType :=
  MkCompilableType vals32_t C_S32.

(** Type signature: val -> val
  *)
Definition valS32TovalS32SymbolType :=
  MkCompilableSymbolType [valS32CompilableType] (Some valS32CompilableType).

Definition Const_valS32_neg :=
  MkPrimitive valS32TovalS32SymbolType
                Val.neg
                (fun es => match es with
                           | [e1] => Ok (C_S32_neg e1) (** Csyntax.Eunop Cop.Oneg x C_S32. *)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** Type signature: val -> val -> val
  *)
Definition valS32TovalS32TovalS32SymbolType :=
  MkCompilableSymbolType [valS32CompilableType; valS32CompilableType] (Some valS32CompilableType).

Definition Const_valS32_add :=
  MkPrimitive valS32TovalS32TovalS32SymbolType
                Val.add
                (fun es => match es with
                           | [e1; e2] => Ok (C_S32_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Val2U64 *******************)

Definition val64_t := val.

Definition val64CompilableType :=
  MkCompilableType val64_t C_U64.

Definition val64_zero := Vlong Int64.zero.

Definition val64SymbolType :=
  MkCompilableSymbolType nil (Some val64CompilableType).

Definition Const_val64_zero := constant val64SymbolType val64_zero C_U64_zero.

(** Type signature: val -> val
  *)
Definition val64Toval64SymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some val64CompilableType).

Definition Const_val64_neg :=
  MkPrimitive val64Toval64SymbolType
                Val.negl
                (fun es => match es with
                           | [e1] => Ok (C_U64_neg e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).


Instance C_val64 : CType val64_t := mkCType _ (cType val64CompilableType).

(** Type signature: val -> val -> option val
    we use `val64_divlu` to replace `Val.divlu`
  *)

Definition val64_divlu (x y: val): val :=
  match Val.divlu x y with
  | Some res => res
  | None => Vundef
  end.

(** Type signature: val -> val -> option val
    we use `val32_modlu` to replace `Val.modlu`
  *)

Definition val64_modlu (x y: val): val :=
  match Val.modlu x y with
  | Some res => res
  | None => Vundef
  end.

Definition Const_val64_add := ltac: (mkprimitive Val.addl (binop_expr Cop.Oadd C_U64)).
Definition Const_val64_sub := ltac: (mkprimitive Val.subl (binop_expr Cop.Osub C_U64)).
Definition Const_val64_mul := ltac: (mkprimitive Val.mull (binop_expr Cop.Omul C_U64)).
Definition Const_val64_div := ltac: (mkprimitive val64_divlu (binop_expr Cop.Odiv C_U64)).
Definition Const_val64_or  := ltac: (mkprimitive Val.orl  (binop_expr Cop.Oor  C_U64)).
Definition Const_val64_and := ltac: (mkprimitive Val.andl (binop_expr Cop.Oand C_U64)).
Definition Const_val64_shl := ltac: (mkprimitive Val.shll (binop_expr Cop.Oshl C_U64)).
Definition Const_val64_shr := ltac: (mkprimitive Val.shrlu (binop_expr Cop.Oshr C_U64)).
Definition Const_val64_mod := ltac: (mkprimitive val64_modlu (binop_expr Cop.Omod C_U64)).
Definition Const_val64_xor := ltac: (mkprimitive Val.xorl (binop_expr Cop.Oxor C_U64)).

(** Type signature: val -> val -> val
  *)
Definition val64Toval64Toval64SymbolType :=
  MkCompilableSymbolType [val64CompilableType; val64CompilableType] (Some val64CompilableType).

Definition Const_val64_shrs :=
  MkPrimitive val64Toval64Toval64SymbolType
                Val.shrl
                (fun es => match es with
                           | [e1; e2] => Ok (C_U64_shr (Csyntax.Ecast  e1 C_S64) e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(******************** Val Type Casting *******************)

(** _to_u32 : vlong_to_vint <==> val_intoflongu
  *)

Definition val_intuoflongu (v: val): val :=
  match v with
  | Vlong n    => Vint (Int.repr (Int64.unsigned n))
  | _          => Vundef
  end.

Definition val64TovalU32SymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some valU32CompilableType).

Definition Const_val64TovalU32 :=
  MkPrimitive val64TovalU32SymbolType
                val_intuoflongu
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U32)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** _to_S32 : vlong_to_vint <==> val_intsoflongu
  *)

Definition val_intsoflongu (v: val): val :=
  match v with
  | Vlong n    => Vint (Int.repr (Int64.unsigned n))
  | _          => Vundef
  end.

Definition val64TovalS32SymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some valS32CompilableType).

Definition Const_val64TovalS32 :=
  MkPrimitive val64TovalS32SymbolType
                val_intsoflongu
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_S32)
                           | _       => Err PrimitiveEncodingFailed
                           end).
(** int64_to_vlong: long -> Vlong
  *)
Definition int64_to_vlong (v: int64): val := Vlong v.

Definition int64Toval64SymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some val64CompilableType).

Definition Const_int64_to_vlong :=
  MkPrimitive int64Toval64SymbolType
                int64_to_vlong
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).

(*
(** int_to_vint: int -> Vint
  *)
Definition sint_to_vint (v: int): val := Vint v.

Definition sint32TovalS32SymbolType :=
  MkCompilableSymbolType [sint32CompilableType] (Some valS32CompilableType).

Definition Const_sint_to_vint:=
  MkPrimitive sint32TovalS32SymbolType
                sint_to_vint
                (fun es => match es with
                           | [e1] => Ok e1
                           | _       => Err PrimitiveEncodingFailed
                           end).*)

(** _to_U64: Val.longofintu
  *)
Definition valU32Toval64SymbolType :=
  MkCompilableSymbolType [valU32CompilableType] (Some val64CompilableType).

Definition Const_valU32Toval64 :=
  MkPrimitive valU32Toval64SymbolType
                Val.longofint
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition Const_valU32Toval64_u :=
  MkPrimitive valU32Toval64SymbolType
                Val.longofintu
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** div_by_zero
  *)
Definition div64_checking (v: val): bool :=
  match v with
  | Vlong n => negb (Int64.eq n Int64.zero)
  | _ => false
  end.

Definition val64ToboolSymbolType :=
  MkCompilableSymbolType [val64CompilableType] (Some boolCompilableType).
(** TODO: maybe we should give the compilableType of val. But it is hard because var is compilable with uint64/uint32/uint16... a union type?
*)
Definition Const_div64_checking :=
  MkPrimitive val64ToboolSymbolType
                div64_checking
                (fun es => match es with
                           | [v] => Ok (Csyntax.Econdition
                                        (Csyntax.Ebinop Cop.Oeq v C_U64_zero C_U64)
                                        (Csyntax.Eval Values.Vfalse Ctypes.type_bool)
                                        (Csyntax.Eval Values.Vtrue Ctypes.type_bool)
                                        Ctypes.type_bool
                                    )
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition div32_checking (v: val): bool :=
  match v with
  | Vint n => negb (Int.eq n Int.zero)
  | _ => false
  end.

Definition valU32ToboolSymbolType :=
  MkCompilableSymbolType [valU32CompilableType] (Some boolCompilableType).
(** TODO: maybe we should give the compilableType of val. But it is hard because var is compilable with uint64/uint32/uint16... a union type?
*)
Definition Const_div32_checking :=
  MkPrimitive valU32ToboolSymbolType
                div32_checking
                (fun es => match es with
                           | [v] => Ok (Csyntax.Econdition
                                        (Csyntax.Ebinop Cop.Oeq v C_U32_zero C_U32)
                                        (Csyntax.Eval Values.Vfalse Ctypes.type_bool)
                                        (Csyntax.Eval Values.Vtrue Ctypes.type_bool)
                                        Ctypes.type_bool
                                    )
                           | _       => Err PrimitiveEncodingFailed
                           end).

(** 
  For 'shrl', 'shll', 'shrul': the shift value must be a Vint, so there is a type casting 
  *)

(** shift64_casting = shift64_checking + val_intoflongu
Definition shift64_casting (v: val): option val :=
  match v with
  | Vlong v => if Int.ltu (Int.repr (Int64.unsigned v)) Int64.iwordsize' then
                 Some (val_intoflongu v)
               else
                 None
  | _       => None
  end.*)
Definition shift64_checking (v: val): bool :=
  match v with
  | Vlong n => Int.ltu (Int.repr (Int64.unsigned n)) Int64.iwordsize'
  | _ => false
  end.

Definition Const_shift64_checking :=
  MkPrimitive val64ToboolSymbolType
                shift64_checking
                (fun es => match es with
                           | [v] => Ok (Csyntax.Econdition
                                        (Csyntax.Ebinop Cop.Olt v C_U64_64 C_U64)
                                        (Csyntax.Eval Values.Vfalse Ctypes.type_bool)
                                        (Csyntax.Eval Values.Vtrue Ctypes.type_bool)
                                        Ctypes.type_bool
                                    )
                           | _       => Err PrimitiveEncodingFailed
                           end).


(** For 'shr', 'shl' and 'shru': the shift value must be less than 32 *)

Definition shift32_checking (v: val): bool :=
  match v with
  | Vint n => Int.ltu n Int.iwordsize
  | _ => false
  end.

Definition Const_shift32_checking :=
  MkPrimitive valU32ToboolSymbolType
                shift32_checking
                (fun es => match es with
                           | [v] => Ok (Csyntax.Econdition
                                        (Csyntax.Ebinop Cop.Olt v C_U32_32 C_U32)
                                        (Csyntax.Eval Values.Vfalse Ctypes.type_bool)
                                        (Csyntax.Eval Values.Vtrue Ctypes.type_bool)
                                        Ctypes.type_bool
                                    )
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition valU32CompilableType := valU32CompilableType.
  Definition Const_valU32_neg := Const_valU32_neg.
  Definition Const_valU32_add := Const_valU32_add.
  Definition Const_valU32_sub := Const_valU32_sub.
  Definition Const_valU32_mul := Const_valU32_mul.
  Definition Const_valU32_div := Const_valU32_div.
  Definition Const_valU32_or  := Const_valU32_or.
  Definition Const_valU32_and := Const_valU32_and.
  Definition Const_valU32_shl := Const_valU32_shl.
  Definition Const_valU32_shr := Const_valU32_shr.
  Definition Const_valU32_mod := Const_valU32_mod.
  Definition Const_valU32_xor := Const_valU32_xor.
  Definition Const_valU32_shrs := Const_valU32_shrs.
  Definition valS32CompilableType := valS32CompilableType.
  Definition Const_valS32_neg := Const_valS32_neg.
  Definition Const_valS32_add := Const_valS32_add.

  Definition val64CompilableType := val64CompilableType.
  Definition Const_val64_zero := Const_val64_zero.
  Definition Const_val64_neg := Const_val64_neg.
  Definition Const_val64_add := Const_val64_add.
  Definition Const_val64_sub := Const_val64_sub.
  Definition Const_val64_mul := Const_val64_mul.
  Definition Const_val64_div := Const_val64_div.
  Definition Const_val64_or  := Const_val64_or.
  Definition Const_val64_and := Const_val64_and.
  Definition Const_val64_shl := Const_val64_shl.
  Definition Const_val64_shr := Const_val64_shr.
  Definition Const_val64_mod := Const_val64_mod.
  Definition Const_val64_xor := Const_val64_xor.
  Definition Const_val64_shrs := Const_val64_shrs.
  
  Definition Const_val64TovalU32 := Const_val64TovalU32.
  Definition Const_val64TovalS32 := Const_val64TovalS32.
  Definition Const_int64_to_vlong := Const_int64_to_vlong.
  Definition Const_valU32Toval64 := Const_valU32Toval64.
  Definition Const_valU32Toval64_u := Const_valU32Toval64_u.
  Definition Const_div64_checking := Const_div64_checking.
  Definition Const_div32_checking := Const_div32_checking.
  Definition Const_shift64_checking := Const_shift64_checking.
  Definition Const_shift32_checking := Const_shift32_checking.
End Exports.
