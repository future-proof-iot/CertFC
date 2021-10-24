From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Nat.

Require Import CoqIntegers DxIntegers.


Module MyList.

  Definition t := list int64_t.
  Definition index_64 (l: t) (idx: int64_t): int64_t := 
    List.nth (Z.to_nat (Integers.Int64.unsigned idx)) l (Integers.Int64.zero).
  Definition index_nat (l: t) (idx: nat): int64_t := 
    List.nth idx l (Integers.Int64.zero).

End MyList.

(** length of MyList should be a extern variable? *)

Definition MyListType := MyList.t.
Definition MyListIndex64 := MyList.index_64.
Definition MyListIndexnat := MyList.index_nat.


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
  MkCompilableSymbolType [MyListCompilableType; int64CompilableType] (Some int64CompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndex64Primitive := 
  MkPrimitive MyListToStateToStateCompilableSymbolType 
              MyListIndex64
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
  Definition myListIndex64Primitive  := myListIndex64Primitive.
  Definition myListIndexnatPrimitive := myListIndexnatPrimitive.
End Exports.
