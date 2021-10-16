From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Errors Values.
From compcert.lib Require Integers.


From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import CoqIntegers DxIntegers DxList64 DxValues DxRegs.

Open Scope string.

Definition state := int64_t. (*This one must be int_64 defined in DxIntegers *)

Definition M (A: Type) := state -> option (A * state).

Definition runM {A: Type} (x: M A) (s: state) := x s.
Definition returnM {A: Type} (a: A) : M A := fun s => Some (a, s).
Definition emptyM {A: Type} : M A := fun s => None.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B :=
  fun s =>
    match runM x s with
    | None => None
    | Some (x', s') => runM (f x') s'
    end.

Definition get : M state := fun s => Some (s, s).
Definition put (s: state) : M unit := fun s' => Some (tt, s).

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.

Open Scope monad_scope.

Definition testadd (a b: state): M state :=
  returnM (Integers.Int64.add a b).

Definition testget (fuel: nat) (init idx: state) (l: MyListType): M state :=
  match fuel with
  | O => do i <- testadd init idx;
          returnM (Integers.Int64.add i int64_two)
  | S nfuel => returnM (MyListGet l idx)
  end.

Definition list_get (l: MyListType) (idx: state): M state :=
  returnM (MyListGet l idx).

Definition mysum (a b: state): M state :=
  returnM (Integers.Int64.add a b).

Fixpoint interpreter1 (fuel: nat) (init idx: state) (l: MyListType){struct fuel}: M state :=
  match fuel with
  | O => returnM init
  | S nfuel =>
    do i <- list_get l idx;
    do s <- mysum init i;
      interpreter1 nfuel s i l
  end.

(** Coq2C: pc -> unsigned int pc := 0; as global variable!
  *)
(* I guess we should know how to use `SymbolIRs`
Definition pc: int32_t := Integers.Int.one.*)

Definition testreg (r:reg): M reg := returnM r.

Definition test_reg_eval (r: reg) (regs: regmap): M val_t :=
  returnM (eval_regmap r regs).

Definition test_reg_upd (r: reg) (v: val_t) (regs: regmap): M regmap :=
  returnM (upd_regmap r v regs).

Close Scope monad_scope.

(***************************************)


GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  DxIntegers.Exports
  DxList64.Exports
  DxValues.Exports
  DxRegs.Exports
  __
  testadd
  testget
  list_get
  mysum
  interpreter1
  testreg
  test_reg_eval
  test_reg_upd
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.
