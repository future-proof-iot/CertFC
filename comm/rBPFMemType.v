From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert Require Import Integers Values Memtype Memory.

Open Scope Z_scope.

(** permission_eq_eq: permission_eq -> permission_eq -> bool
  *)

Definition perm_ge (x y: permission): bool := if (Mem.perm_order_dec x y) then true else false.