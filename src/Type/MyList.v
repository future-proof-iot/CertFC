From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx Require Import ResultMonad IR.


(*
Coq src:
  l: boundedlist A; //{xs:list A; len:nat}
  List.nth n l default;
  List.length l;
  List.hd default l;
  ..


C dst:
  c_A l[len];
  if (n < len) l[n] else default;
  len;
  if (a = nil) default else a[0]; //len = 0 is impossible in C?
  ..
*)

Definition Cint64 := Ctypes.Tlong Ctypes.Unsigned Ctypes.noattr.

Definition Cpointer := Ctypes.Tpointer Cint64 Ctypes.noattr.

(*
Parameter len : nat. (*C global variable: int len := C  (dx)constant *)

Definition Carray (cty: Ctypes.type) (len: nat) : Ctypes.type := Ctypes.Tarray cty (Z.of_nat len) Ctypes.noattr.

Definition arraylist64 := list Integers.int64.

Definition arraylistCompilableType :=
  MkCompilableType arraylist64 (Carray Cint64 len).

Definition PrimitiveType := MkPrimitive...*)

Definition listInt64 := list Integers.int64.

Definition listCompilableType :=
  MkCompilableType listInt64 Cpointer.

Definition null : Csyntax.expr :=
  Csyntax.Eval Values.Vnullptr Cpointer.

(* plus_plus p <=> p++ *)
Definition plus_plus (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Epreincr Cop.Incr x Cint64.

Definition listSymbolType :=
  MkCompilableSymbolType nil (Some listCompilableType).

Definition listMatchableType :=
  MkMatchableType listCompilableType
    (fun x cases =>
      match cases with
      | [caseNil; caseTl] => 
        Ok (Csyntax.Sifthenelse
              (Csyntax.Ebinop Cop.Oeq x null Cpointer)
              caseNil caseTl)
      | _ => Err MatchEncodingFailed
      end)
    [[]; [plus_plus]]
    [[]; [listCompilableType]]
    (fun m A l WhenNil WhenTl =>
      match l with
      | nil => WhenNil
      | hd :: tl => WhenTl tl
      end).

Definition list_null := constant listSymbolType nil null.

Module Exports.
  Definition listCompilableType := listCompilableType.
  Definition listSymbolType := listSymbolType.
  Definition list_null := list_null.
End Exports.
