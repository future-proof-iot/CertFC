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
  Definition index (l: t) (idx: int64_t): int64_t := 
    List.nth (Z.to_nat (Integers.Int64.unsigned idx)) l (Integers.Int64.zero).

End MyList.

(** length of MyList should be a extern variable? *)

Definition MyListType := MyList.t.
Definition MyListIndex := MyList.index.


Definition MySum (a b: int64_t): int64_t := Integers.Int64.add a b.

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

(** Type Signature: MyList.t -> MyList.t *)
Definition MyListToMyListCompilableSymbolType :=
  MkCompilableSymbolType [MyListCompilableType] (Some MyListCompilableType).

(** Type for MyList.t -> u64_t -> u64_t *)
Definition MyListToStateToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyListCompilableType; DxIntegers.int64CompilableType] (Some DxIntegers.int64CompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myListIndexPrimitive := 
  MkPrimitive MyListToStateToStateCompilableSymbolType 
              MyListIndex
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition MyListCompilableType := MyListCompilableType.
  Definition myListIndexPrimitive := myListIndexPrimitive.
End Exports.
