From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Errors Values.
From compcert.lib Require Integers.


From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import CoqIntegers DxIntegers DxList64 DxValues DxRegs DxZ DxOpcode.

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
          returnM (Integers.Int64.add i int64_2)
  | S nfuel => returnM (MyListIndex l idx)
  end.

Definition list_get (l: MyListType) (idx: state): M state :=
  returnM (MyListIndex l idx).

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
(* I guess we should know how to use `SymbolIRs`*)
Definition pc: uint32_t := Integers.Int.one.

Definition regs: regmap := init_regmap.

Definition regs_st: regs_state := init_regs_state.

Definition testreg (r:reg): M reg := returnM r.

Definition return0 : M state := returnM Integers.Int64.zero.

Definition return1 : M state := returnM Integers.Int64.one.

Definition return4 : M state := returnM int64_64.

Definition return10 : M state := returnM Integers.Int64.zero.

Definition test_match_reg (r: reg): M state :=
  match r with
  | R0 => return0
  | R1 => return1
  | R4 => return4
  | _ =>  return10
  end.

Definition test_reg_eval (r: reg) (regs: regmap): M val_t :=
  returnM (eval_regmap r regs).

Definition test_reg_upd (r: reg) (v: val_t) (regs: regmap): M regmap :=
  returnM (upd_regmap r v regs).

Definition test_match_nat (n: nat): M state :=
  match n with
  | O => return0
  | 1%nat => return1
  | 2%nat => return10
  | _ => return0
  end.

Definition test_Z: M Z := returnM (z_0x07).

Definition my_get_opcode (i:int64_t):M int64_t := returnM (Integers.Int64.and i (Integers.Int64.repr z_0xff)).

Definition test_z_to_opcode (i:int64_t): M opcode := returnM (z_to_opcode (get_opcode i)).

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
  DxZ.Exports
  DxOpcode.Exports
  pc
  regs
  init_regs_state
  __
  testadd
  testget
  list_get
  mysum
  interpreter1
  testreg
  return0
  return1
  return4
  return10
  test_match_reg
  test_reg_eval
  test_reg_upd
  test_match_nat
  test_Z
  my_get_opcode
  test_z_to_opcode
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.
