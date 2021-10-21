From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
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

Definition list_get (li: MyListType) (idx: state): M state :=
  returnM (MyListIndex li idx).

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
(*
Definition pc: uint32_t := Integers.Int.one.*)

(*
Definition regs: regmap := init_regmap.*)

Axiom pc: int64_t.
Axiom regs: regmap.

Definition default_regs := returnM init_regmap.

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

Definition eval_reg (r: reg): M val64_t :=
  returnM (eval_regmap r regs).


Definition upd_reg (r: reg) (v: val64_t): M regmap :=
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
Definition get_immediate (i:int64_t):M vals32_t := returnM (val_intsoflongu (int64_to_vlong (Int64.shru i (Int64.repr z_32)))).

Definition test_int_shift (i j:int64_t): M int64_t := returnM (Integers.Int64.shr i j).

Definition ins_to_opcode (i: int64_t): M opcode :=
  do op_z <- get_opcode i;
    returnM (z_to_opcode op_z).

Definition ins_to_dst_reg (i: int64_t): M reg :=
  do dst_z <- get_dst i;
    returnM (z_to_reg dst_z).

Definition ins_to_src_reg (i: int64_t): M reg :=
  do src_z <- get_src i;
    returnM (z_to_reg src_z).

(** show loc < List.length l *)
Definition step (l: MyListType): M regmap :=
  do ins <- list_get l pc;
  do op <- ins_to_opcode ins;
  do dst <- ins_to_dst_reg ins;
  do src <- ins_to_src_reg ins;
  do ofs <- get_offset ins;
  do imm <- get_immediate ins;
  do dst64 <- eval_reg dst;
  do src64 <- eval_reg src;
  match op with
  (** ALU64 *)
  | op_BPF_ADD64i   => upd_reg dst (Val.addl    dst64 (Val.longofintu imm))
  | op_BPF_ADD64r   => upd_reg dst (Val.addl    dst64 src64)
  | op_BPF_SUB64i   => upd_reg dst (Val.subl    dst64 (Val.longofintu imm))
  | op_BPF_SUB64r   => upd_reg dst (Val.subl    dst64 src64)
  | op_BPF_MUL64i   => upd_reg dst (Val.mull    dst64 (Val.longofintu imm))
  | op_BPF_MUL64r   => upd_reg dst (Val.mull    dst64 src64)
  (**r how to generate exit or printf function ? *)
  | op_BPF_DIV64i   => upd_reg dst (val64_divlu dst64 (Val.longofintu imm))
  | op_BPF_DIV64r   => upd_reg dst (val64_divlu dst64 src64)
  | op_BPF_OR64i    => upd_reg dst (Val.orl     dst64 (Val.longofintu imm))
  | op_BPF_OR64r    => upd_reg dst (Val.orl     dst64 src64)
  | op_BPF_AND64i   => upd_reg dst (Val.andl    dst64 (Val.longofintu imm))
  | op_BPF_AND64r   => upd_reg dst (Val.andl    dst64 src64)
  | op_BPF_LSH64i   => upd_reg dst (Val.shll    dst64 (Val.longofintu imm))
  | op_BPF_LSH64r   => upd_reg dst (Val.shll    dst64 src64)
  | op_BPF_RSH64i   => upd_reg dst (Val.shrlu   dst64 (Val.longofintu imm))
  | op_BPF_RSH64r   => upd_reg dst (Val.shrlu   dst64 src64)
  | op_BPF_NEG64    => upd_reg dst (Val.negl    dst64)
  | op_BPF_MOD64i   => upd_reg dst (val64_modlu dst64 (Val.longofintu imm))
  | op_BPF_MOD64r   => upd_reg dst (val64_modlu dst64 src64) (**r same *)
  | op_BPF_XOR64i   => upd_reg dst (Val.xorl    dst64 (Val.longofintu imm))
  | op_BPF_XOR64r   => upd_reg dst (Val.xorl    dst64 src64)
  | op_BPF_MOV64i   => upd_reg dst (Val.longofintu imm)
  | op_BPF_MOV64r   => upd_reg dst src64
  | op_BPF_ARSH64i  => upd_reg dst (Val.shrl    dst64 (Val.longofintu imm))
  | op_BPF_ARSH64r  => upd_reg dst (Val.shrl    dst64 src64)
  (*ALU32*)
  | op_BPF_ADD32i   =>
      upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) imm))
  | op_BPF_ADD32r   =>
      upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_SUB32i   =>
      upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) imm))
  | op_BPF_SUB32r   =>
      upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_MUL32i   =>
      upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) imm))
  | op_BPF_MUL32r   =>
      upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_DIV32i   =>
      upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) imm))
  | op_BPF_DIV32r   =>
      upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_OR32i   =>
      upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) imm))
  | op_BPF_OR32r   =>
      upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_AND32i   =>
      upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) imm))
  | op_BPF_AND32r   =>
      upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_LSH32i   =>
      upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) imm))
  | op_BPF_LSH32r   =>
      upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_RSH32i   =>
      upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) imm))
  | op_BPF_RSH32r   =>
      upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_NEG32    =>
      upd_reg dst (Val.longofintu (Val.neg (val_intuoflongu (dst64))))
  | op_BPF_MOD32i   =>
      upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) imm))
  | op_BPF_MOD32r   =>
      upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_XOR32i   =>
      upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) imm))
  | op_BPF_XOR32r   =>
      upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) (val_intuoflongu src64)))
  | op_BPF_MOV32i   => upd_reg dst imm
  | op_BPF_MOV32r   => upd_reg dst (val_intuoflongu src64)
  | op_BPF_ARSH32i   =>
      upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) imm))
  | op_BPF_ARSH32r   =>
      upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) (val_intuoflongu src64)))
  | _ => default_regs
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
  testget*)(*
  mysum
  interpreter1
  testreg
  return0
  return1
  return4
  return10
  test_match_reg
  test_int_shift
  test_match_nat
  test_Z*)
  list_get
  eval_reg
  upd_reg
  get_opcode
  get_dst
  get_src
  get_offset
  get_immediate
  ins_to_opcode
  ins_to_dst_reg
  ins_to_src_reg
  step
.

Definition dxModuleTest := makeDXModuleWithoutMain SymbolIRs.