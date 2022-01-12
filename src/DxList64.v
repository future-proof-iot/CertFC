From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

From bpf.comm Require Import List64.
From bpf.src Require Import CoqIntegers DxIntegers.

(*
Module MyList.

  Definition t := list int64_t.
  Definition index_s32 (l: t) (idx: sint32_t): int64_t := 
    List.nth (Z.to_nat (Integers.Int.signed idx)) l (Integers.Int64.zero).
  Definition index_nat (l: t) (idx: nat): int64_t := 
    List.nth idx l (Integers.Int64.zero).

End MyList.

(** length of MyList should be a extern variable? *)

Definition MyListType := MyList.t.
Definition MyListIndexs32 := MyList.index_s32.
Definition MyListIndexnat := MyList.index_nat.

Definition default_list: MyListType :=  [].
*)

(******************** Dx Related *******************)

(** "Mapping relations from Coq to C":
  Coq:          -> C:
  l:list state  -> uint64_t *l
  get l idx     -> *(l+idx)
 *)

Definition get_index (x idx: Csyntax.expr): Csyntax.expr :=
  Csyntax.Eindex x idx C_U64.

(** Coq2C: l:list u64_t  -> uint64_t *l *)
Definition MyListCompilableType :=
  MkCompilableType MyListType C_U64_pointer.

(** Type for MyList.t -> u64_t -> u64_t *)
Definition MyListToStateToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyListCompilableType; sint32CompilableType] (Some int64CompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndexs32Primitive := 
  MkPrimitive MyListToStateToStateCompilableSymbolType 
              MyListIndexs32
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** Type for MyList.t -> nat -> u64_t *)
Definition MyListToNatToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyListCompilableType; natCompilableType] (Some int64CompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndexnatPrimitive := 
  MkPrimitive MyListToNatToStateCompilableSymbolType 
              MyListIndexnat
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition MyListCompilableType    := MyListCompilableType.
  Definition myListIndexs32Primitive := myListIndexs32Primitive.
  Definition myListIndexnatPrimitive := myListIndexnatPrimitive.
End Exports.
