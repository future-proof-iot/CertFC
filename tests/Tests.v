From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Errors Values.
From compcert.lib Require Import Integers.


From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.
Require Import Int16 CoqIntegers DxIntegers DxList64 DxValues DxRegs DxZ DxOpcode.

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

Definition default_regs := returnM regs.

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

Definition get_opcode (i:int64_t):M Z := returnM (Int64.unsigned (Int64.and i (Int64.repr z_0xff))).
Definition get_dst (i:int64_t):M Z := returnM (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr z_0xfff)) (Int64.repr z_8))).
Definition get_src (i:int64_t):M Z := returnM (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr z_0xffff)) (Int64.repr z_12))).
Definition get_offset (i:int64_t ):M sint16_t := returnM (Int16.repr (Int64.unsigned (Int64.shru (Int64.shl i (Int64.repr z_32)) (Int64.repr z_48)))).
Definition get_immediate (i:int64_t):M sint32_t := returnM (Int.repr (Int64.unsigned (Int64.shru i (Int64.repr z_32)))).

Definition test_int_shift (i j:int64_t): M int64_t := returnM (Integers.Int64.shr i j).

Definition ins_to_opcode (ins: int64_t): M opcode :=
  do op_z <- get_opcode ins;
    returnM (z_to_opcode op_z).

Definition ins_to_dst_reg (ins: int64_t): M reg :=
  do dst_z <- get_dst ins;
    returnM (z_to_reg dst_z).

Definition ins_to_src_reg (ins: int64_t): M reg :=
  do src_z <- get_src ins;
    returnM (z_to_reg src_z).

(** show loc < List.length l *)
Definition step (l: MyListType) (loc: int64_t) (st: regmap): M regmap :=
  do ins <- list_get l loc;
  do op <- ins_to_opcode ins;
  do dst <- ins_to_dst_reg ins;
  do src <- ins_to_src_reg ins;
  do ofs <- get_offset ins;
  do imm <- get_immediate ins;
  match op with
  | op_BPF_NEG32 => 
      do dst64 <- test_reg_eval dst st;
      test_reg_upd dst (Values.Val.longofintu (Values.Val.neg (val_intoflongu (dst64)))) st
  | op_BPF_NEG64 => default_regs
  | op_BPF_ADD32r => default_regs
  | op_BPF_ADD32i => default_regs
  | op_BPF_ADD64r => default_regs
  | op_BPF_ADD64i => default_regs
  | op_BPF_RET => default_regs
  | op_BPF_ERROR_INS => default_regs
  end.

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
  default_regs
  __
  (*testadd
  testget*)
  list_get(*
  mysum
  interpreter1
  testreg*)
  return0
  return1
  return4
  return10
  test_match_reg
  test_reg_eval
  test_reg_upd
  test_match_nat
  test_Z
  get_opcode
  get_dst
  get_src
  get_offset
  get_immediate
  test_int_shift
  ins_to_opcode
  ins_to_dst_reg
  ins_to_src_reg
  step
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.
