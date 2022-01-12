From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Import Integers.

From bpf.comm Require Import Int16.

(** Coq2C: Values.val -> unsigned long long or unsigned int
  *)

(******************** Val2PTR *******************)


Definition comp_eq_ptr8_zero (x: val): bool :=
  match x with
  | Vint n1 => Int.eq n1 Int.zero
  | _ => false
  end.

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

Definition comp_eq_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => Int.eq n1 n2
  | _, _ => false
  end.

Definition comp_ne_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => negb (Int.eq n1 n2)
  | _, _ => false
  end.

Definition compu_lt_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => Int.ltu n1 n2
  | _, _ => false
  end.

Definition compu_le_32 (x y: val): bool :=
  match x, y with
  | Vint n1, Vint n2 => negb (Int.ltu n2 n1)
  | _, _ => false
  end.


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
(** To avoid defining the matchableType of comparison in dx, we define unique comparison functions *)

Definition compl_eq (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.eq n1 n2
  | _, _ => false
  end.
Definition compl_ne (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.eq n1 n2)
  | _, _ => false
  end.
Definition compl_lt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.lt n1 n2
  | _, _ => false
  end.
Definition compl_le (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.lt n2 n1)
  | _, _ => false
  end.
Definition compl_gt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.lt n2 n1
  | _, _ => false
  end.
Definition compl_ge (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.lt n1 n2)
  | _, _ => false
  end.
Definition complu_lt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.ltu n1 n2
  | _, _ => false
  end.
Definition complu_le (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.ltu n2 n1)
  | _, _ => false
  end.
Definition complu_gt (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => Int64.ltu n2 n1
  | _, _ => false
  end.
Definition complu_ge (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.ltu n1 n2)
  | _, _ => false
  end.
Definition complu_set (x y: val): bool :=
  match x, y with
  | Vlong n1, Vlong n2 => negb (Int64.eq (Int64.and n1 n2) Int64.zero)
  | _, _ => false
  end.

(******************** Val Type Casting *******************)

(** ptr2valu32: ptr -> u32

*)
(*
Definition ptr2valu32 (ptr: valptr32_t): valu32_t :=
  match ptr with
  | Vptr _ _ => here we need memory_region information...*)

(** sint16_to_vlong: sint16_t -> Val
    *)
Definition sint16_to_vlong (i:int16): val :=
  Vlong (Int64.repr (Int16.signed i)).

(** _to_u32 : vlong_to_vint <==> val_intoflongu
  *)

Definition val_intuoflongu (v: val): val :=
  match v with
  | Vlong n    => Vint (Int.repr (Int64.unsigned n))
  | _          => Vundef
  end.

(** _to_S32 : vlong_to_vint <==> val_intsoflongu
  *)

Definition val_intsoflongu (v: val): val :=
  match v with
  | Vlong n    => Vint (Int.repr (Int64.unsigned n))
  | _          => Vundef
  end.
(** sint32_to_vlong: sint32 -> Vlong
  *)
Definition sint32_to_vint (v: int): val := Vint v.
(** int64_to_vlong: long -> Vlong
  *)
Definition int64_to_vlong (v: int64): val := Vlong v.

Definition int64_to_int8 (x: int64): byte := Byte.repr (Int64.unsigned x).

(** sint16_to_uint64: sint16_t -> uint64_t
  *)
Definition sint16_to_int64 (x: int16): int64 := Int64.repr (Int16.signed x).

(** sint16_to_sint32: sint16_t -> sint32_t
  *)
Definition sint16_to_sint32 (x: int16): int := Int.repr (Int16.signed x).

(** int64_to_sint16: int64_t -> sint16_t
  *)
Definition int64_to_sint16 (x: int64): int16 := Int16.repr (Int64.unsigned x).

(** int64_to_sint32: int64_t -> sint32_t
  *)
Definition int64_to_sint32 (x: int64): int := Int.repr (Int64.unsigned x).

Definition Int_le (x y: int): bool := negb (Int.lt y x).