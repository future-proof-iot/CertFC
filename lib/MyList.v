From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.

Require MyInt64.

Definition state := MyInt64.int64_t.

Module MyList1.

  Definition t := list state.
  Definition get (l: t) (idx: state): state := 
    List.nth (Z.to_nat (Integers.Int64.unsigned idx)) l (Integers.Int64.zero).

  (*Definition get (l: t) (idx: state): M state := 
    match List.nth_error l (Z.to_nat (Integers.Int64.unsigned idx)) with
    | Some res => returnM res
    | None => emptyM
    end.*)

End MyList1.

Definition MyListType := MyList1.t.
Definition MyListGet := MyList1.get.

(*
Module MyList2.

  Definition t := list state.
  Definition get (l: t) (idx: state): M (Values.val) := 
    match List.nth_error l (Z.to_nat (Integers.Int64.unsigned idx)) with
    | Some res => returnM (Values.Vlong res)
    | None => emptyM
    end.

End MyList2.
*)

Definition MySum (a b: state): state := MyInt64.C_U64_add a b.

(** "Mapping relations from Coq to C":
  Coq:          -> C:
  l:list state  -> uint64_t *l
  get l idx     -> *(l+idx)
 *)
Definition C_U64 := Ctypes.Tlong Ctypes.Unsigned Ctypes.noattr.

Definition Cpointer := Ctypes.Tpointer C_U64 Ctypes.noattr.

Definition get_index (x idx: Csyntax.expr): Csyntax.expr :=
  Csyntax.Eindex x idx C_U64.


(** Coq2C: l:list state  -> uint64_t *l *)
Definition MyList1CompilableType :=
  MkCompilableType MyListType Cpointer.

(*
Definition MyListMatchableType :=
  MkMatchableType MyList1CompilableType
    (fun cnd brchs =>
      match brchs with
      | [brchThen;brchElse] => Ok (Csyntax.Sifthenelse cnd brchThen brchElse)
      | _                   => Err MatchEncodingFailed
      end)
    [[];[]]
    [[];[]]
    (fun m A b whenTrue whenFalse => if b then whenTrue else whenFalse)
.*)

(** Type for MyList.t -> MyList.t *)
Definition MyListToMyListCompilableSymbolType :=
  MkCompilableSymbolType [MyList1CompilableType] (Some MyList1CompilableType).

(** Type for MyList.t -> state -> state *)
Definition MyListToStateToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyList1CompilableType; MyInt64.int64CompilableType] (Some MyInt64.int64CompilableType).

(** Type for state -> state -> state *)
Definition StateToStateToStateCompilableSymbolType :=
  MkCompilableSymbolType [MyInt64.int64CompilableType; MyInt64.int64CompilableType] (Some MyInt64.int64CompilableType).

(** Coq2C: get l idx -> *(l+idx) *)
Definition myList1GetPrimitive := 
  MkPrimitive MyListToStateToStateCompilableSymbolType 
              MyListGet
              (fun es => match es with
                         | [e1; e2] => Ok (get_index e1 e2)
                         | _   => Err PrimitiveEncodingFailed
                         end).

(** Coq2C: MySum a b -> a + b *)
Definition myList1SumPrimitive := 
  MkPrimitive StateToStateToStateCompilableSymbolType 
              MySum
              (fun es => match es with
                         | [e1; e2] => Ok (Csyntax.Ebinop Cop.Oadd e1 e2 C_U64)
                         | _   => Err PrimitiveEncodingFailed
                         end).

Module Exports.
  Definition MyList1CompilableType := MyList1CompilableType.
  Definition myList1GetPrimitive := myList1GetPrimitive.
  Definition myList1SumPrimitive := myList1SumPrimitive.
End Exports.
