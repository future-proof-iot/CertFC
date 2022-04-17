From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Import Integers.


Module MyList.

  Definition t := list int64.
  Definition index_s32 (l: t) (idx: int): int64 := 
    match List.nth_error l (Z.to_nat (Int.unsigned idx)) with
    | Some i => i
    | None => Integers.Int64.zero
    end.
  Definition index_nat (l: t) (idx: nat): int64 := 
    List.nth idx l Integers.Int64.zero.

End MyList.

(** length of MyList should be a extern variable? *)

Definition MyListType := MyList.t.
Definition MyListIndexs32 := MyList.index_s32.
Definition MyListIndexnat := MyList.index_nat.

Definition default_list: MyListType :=  [].