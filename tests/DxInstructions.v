From compcert Require Import Integers Values.

From dx.Type Require Import Bool Nat.

Require Import DxIntegers DxList64 DxRegs DxState DxValues DxOpcode.

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
      upd_reg dst (Val.longofintu (Val.neg (val_intoflongu (dst64)))) st
  | BPF_NEG64 dst     =>
    do dst64 <- (eval_reg dst st) ;
      upd_reg dst (Val.negl (dst64)) st
  | BPF_ADD32r dst src =>
    do dst64 <- eval_reg dst st;
    do src64 <- eval_reg src st;
      upd_reg dst (Val.longofintu (Val.add (val_intoflongu dst64) (val_intoflongu src64))) st
  | BPF_ADD32i dst i   => 
    do dst64 <- eval_reg dst st;
      upd_reg dst (Val.longofintu (Val.add (val_intoflongu dst64) (Vint i))) st
  | BPF_ADD64r dst src => 
    do dst64 <- eval_reg dst st;
    do src64 <- eval_reg src st;
      upd_reg dst (Val.addl dst64 src64) st
  | BPF_ADD64i dst i   => 
    do dst64 <- eval_reg dst st;
      upd_reg dst (Val.addl dst64 (Val.longofint (Vint i))) st
  | BPF_RET => default_MrBPF
  end.

(** show loc < List.length l *)
Definition step (l: MyListType) (loc: nat) (st: state): MrBPF state :=
  match op

Close Scope monad_scope.


