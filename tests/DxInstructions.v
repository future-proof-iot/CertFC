From compcert Require Import Integers Values.

From dx.Type Require Import Bool Nat.

Require Import Int16 DxIntegers DxList64 DxRegs DxState DxValues DxOpcode DxZ DxState.

From Coq Require Import ZArith.

Definition imm := sint32_t.
Definition off := sint16_t.

Inductive instruction: Type :=
  | BPF_NEG32    : reg -> instruction
  | BPF_NEG64    : reg -> instruction
  | BPF_ADD32r   : reg -> reg -> instruction
  | BPF_ADD32i   : reg -> imm -> instruction
  | BPF_ADD64r   : reg -> reg -> instruction
  | BPF_ADD64i   : reg -> imm -> instruction
  | BPF_RET      : instruction.

(** TODO: regarding the decode function: from int64 to bpf_instruction
  from: https://github.com/bergzand/RIOT/blob/10cecc628e89442777f2a798f6763e3f55ac9731/sys/include/bpf/instruction.h#L89

  typedef struct __attribute__((packed)) {
    uint8_t opcode;
    unsigned dst:4;
    unsigned src:4;
    int16_t offset;
    int32_t immediate;
} bpf_instruction_t;

In C, because `bpf_instruction_t` is int64 and it is a natural mapping from int64 bpf_instruction in C memory model,

However, compcert doesn't support `packed`, so we only can get a:

  typedef struct {
    uint8_t opcode;
    uint8_t dst_src; //here we need to translate it into above/similar structure
    int16_t offset;
    int32_t immediate;
} bpf_instruction_t;

and a decode function to get:

  typedef struct {
    uint8_t opcode;
    uint8_t dst;
    uint8_t src; //uint8_t or unsigned is ok
    int16_t offset;
    int32_t immediate;
} bpf_instruction_t;


There are two ways to do decode: 
  - loop exists: decode once
  - no loop: decode when necessary
*)

Open Scope monad_scope.

Definition step (ins:instruction) (next_ins: option int64) (st: state) : MrBPF state :=
  match ins with
  | BPF_NEG32 dst     =>
    do dst64 <- (eval_reg dst st) ;
      upd_reg dst (Val.longofintu (Val.neg (val_intuoflongu (dst64)))) st
  | BPF_NEG64 dst     =>
    do dst64 <- (eval_reg dst st) ;
      upd_reg dst (Val.negl (dst64)) st
  | BPF_ADD32r dst src =>
    do dst64 <- eval_reg dst st;
    do src64 <- eval_reg src st;
      upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | BPF_ADD32i dst i   => 
    do dst64 <- eval_reg dst st;
      upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) (Vint i))) st
  | BPF_ADD64r dst src => 
    do dst64 <- eval_reg dst st;
    do src64 <- eval_reg src st;
      upd_reg dst (Val.addl dst64 src64) st
  | BPF_ADD64i dst i   => 
    do dst64 <- eval_reg dst st;
      upd_reg dst (Val.addl dst64 (Val.longofint (Vint i))) st
  | BPF_RET => default_MrBPF
  end.

Definition get_opcode (i:int64_t):MrBPF Z := returnM (Int64.unsigned (Int64.and i (Int64.repr z_0xff))).
Definition get_dst (i:int64_t):MrBPF Z := returnM (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr z_0xfff)) (Int64.repr z_8))).
Definition get_src (i:int64_t):MrBPF Z := returnM (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr z_0xffff)) (Int64.repr z_12))).
Definition get_offset (i:int64_t ):MrBPF sint16_t := returnM (Int16.repr (Int64.unsigned (Int64.shru (Int64.shl i (Int64.repr z_32)) (Int64.repr z_48)))).
Definition get_immediate (i:int64_t):MrBPF vals32_t := returnM (val_intsoflongu (int64_to_vlong (Int64.shru i (Int64.repr z_32)))).

Definition list_get (l: MyListType) (idx: int64_t): MrBPF int64_t :=
  returnM (MyListIndex l idx).

Definition ins_to_opcode (ins: int64_t): MrBPF opcode :=
  do op_z <- get_opcode ins;
    returnM (z_to_opcode op_z).

Definition ins_to_dst_reg (ins: int64_t): MrBPF reg :=
  do dst_z <- get_dst ins;
    returnM (z_to_reg dst_z).

Definition ins_to_src_reg (ins: int64_t): MrBPF reg :=
  do src_z <- get_src ins;
    returnM (z_to_reg src_z).

(** show loc < List.length l *)
Definition stepM (l: MyListType) (loc: int64_t) (st: state): MrBPF state :=
  do ins <- list_get l loc;
  do op <- ins_to_opcode ins;
  do dst <- ins_to_dst_reg ins;
  do src <- ins_to_src_reg ins;
  do dst64 <- eval_reg dst st;
  do src64 <- eval_reg src st;
  do ofs <- get_offset ins; (* optiomiz...**)
  do imm <- get_immediate ins;
  match op with
  (** ALU64 *)
  | op_BPF_ADD64i   => upd_reg dst (Val.addl    dst64 (Val.longofintu imm)) st
  | op_BPF_ADD64r   => upd_reg dst (Val.addl    dst64 src64) st
  | op_BPF_SUB64i   => upd_reg dst (Val.subl    dst64 (Val.longofintu imm)) st
  | op_BPF_SUB64r   => upd_reg dst (Val.subl    dst64 src64) st
  | op_BPF_MUL64i   => upd_reg dst (Val.mull    dst64 (Val.longofintu imm)) st
  | op_BPF_MUL64r   => upd_reg dst (Val.mull    dst64 src64) st
  (**r how to generate exit or printf function ? *)
  | op_BPF_DIV64i   => upd_reg dst (val64_divlu dst64 (Val.longofintu imm)) st 
  | op_BPF_DIV64r   => upd_reg dst (val64_divlu dst64 src64) st
  | op_BPF_OR64i    => upd_reg dst (Val.orl     dst64 (Val.longofintu imm)) st
  | op_BPF_OR64r    => upd_reg dst (Val.orl     dst64 src64) st
  | op_BPF_AND64i   => upd_reg dst (Val.andl    dst64 (Val.longofintu imm)) st
  | op_BPF_AND64r   => upd_reg dst (Val.andl    dst64 src64) st
  | op_BPF_LSH64i   => upd_reg dst (Val.shll    dst64 (Val.longofintu imm)) st
  | op_BPF_LSH64r   => upd_reg dst (Val.shll    dst64 src64) st
  | op_BPF_RSH64i   => upd_reg dst (Val.shrlu   dst64 (Val.longofintu imm)) st
  | op_BPF_RSH64r   => upd_reg dst (Val.shrlu   dst64 src64) st
  | op_BPF_NEG64    => upd_reg dst (Val.negl    dst64) st
  | op_BPF_MOD64i   => upd_reg dst (val64_modlu dst64 (Val.longofintu imm)) st
  | op_BPF_MOD64r   => upd_reg dst (val64_modlu dst64 src64) st (**r same *)
  | op_BPF_XOR64i   => upd_reg dst (Val.xorl    dst64 (Val.longofintu imm)) st
  | op_BPF_XOR64r   => upd_reg dst (Val.xorl    dst64 src64) st
  | op_BPF_MOV64i   => upd_reg dst (Val.longofintu imm) st
  | op_BPF_MOV64r   => upd_reg dst src64 st
  | op_BPF_ARSH64i  => upd_reg dst (Val.shrl    dst64 (Val.longofintu imm)) st
  | op_BPF_ARSH64r  => upd_reg dst (Val.shrl    dst64 src64) st
  (*ALU32*)
  | op_BPF_ADD32i   =>
      upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) imm)) st
  | op_BPF_ADD32r   =>
      upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_SUB32i   =>
      upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) imm)) st
  | op_BPF_SUB32r   =>
      upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_MUL32i   =>
      upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) imm)) st
  | op_BPF_MUL32r   =>
      upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_DIV32i   =>
      upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) imm)) st
  | op_BPF_DIV32r   =>
      upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_OR32i   =>
      upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) imm)) st
  | op_BPF_OR32r   =>
      upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_AND32i   =>
      upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) imm)) st
  | op_BPF_AND32r   =>
      upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_LSH32i   =>
      upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) imm)) st
  | op_BPF_LSH32r   =>
      upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_RSH32i   =>
      upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) imm)) st
  | op_BPF_RSH32r   =>
      upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_NEG32    =>
      upd_reg dst (Val.longofintu (Val.neg (val_intuoflongu (dst64)))) st
  | op_BPF_MOD32i   =>
      upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) imm)) st
  | op_BPF_MOD32r   =>
      upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_XOR32i   =>
      upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) imm)) st
  | op_BPF_XOR32r   =>
      upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) (val_intuoflongu src64))) st
  | op_BPF_MOV32i   => upd_reg dst imm st
  | op_BPF_MOV32r   => upd_reg dst (val_intuoflongu src64) st
  | op_BPF_ARSH32i  =>
      upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) imm)) st
  | op_BPF_ARSH32r  =>
      upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) (val_intuoflongu src64))) st
  (**Branch: 23 *)(*
  | op_BPF_JA       => 
  | op_BPF_JEQi
  | op_BPF_JEQr
  | op_BPF_JGTi
  | op_BPF_JGTr
  | op_BPF_JGEi
  | op_BPF_JGEr
  | op_BPF_JLTi
  | op_BPF_JLTr
  | op_BPF_JLEi
  | op_BPF_JLEr
  | op_BPF_JSETi
  | op_BPF_JSETr
  | op_BPF_JNEi
  | op_BPF_JNEr
  | op_BPF_JSGTi
  | op_BPF_JSGTr
  | op_BPF_JSGEi
  | op_BPF_JSGEr
  | op_BPF_JSLTi
  | op_BPF_JSLTr
  | op_BPF_JSLEi
  | op_BPF_JSLEr*)
  | op_BPF_RET       => default_MrBPF
  | _ => default_MrBPF
  end.

Close Scope monad_scope.


