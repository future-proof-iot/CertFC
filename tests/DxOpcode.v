From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers.

From dx Require Import ResultMonad IR.

Require Import CoqIntegers DxIntegers InfComp GenMatchable.

Open Scope Z_scope.

Inductive opcode_alu64_imm: Type := (**r 0xX7 *)
  (** ALU64:13 *)
  | op_BPF_ADD64i
  | op_BPF_SUB64i
  | op_BPF_MUL64i
  | op_BPF_DIV64i
  | op_BPF_OR64i
  | op_BPF_AND64i
  | op_BPF_LSH64i
  | op_BPF_RSH64i
  | op_BPF_NEG64
  | op_BPF_MOD64i
  | op_BPF_XOR64i
  | op_BPF_MOV64i
  | op_BPF_ARSH64i
  | op_BPF_ALU64_IMM_ILLEGAL_INS.


Definition int64_to_opcode_alu64_imm (ins: int64_t): opcode_alu64_imm :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x07 => op_BPF_ADD64i
    | 0x17 => op_BPF_SUB64i
    | 0x27 => op_BPF_MUL64i
    | 0x37 => op_BPF_DIV64i
    | 0x47 => op_BPF_OR64i
    | 0x57 => op_BPF_AND64i
    | 0x67 => op_BPF_LSH64i
    | 0x77 => op_BPF_RSH64i
    | 0x87 => op_BPF_NEG64
    | 0x97 => op_BPF_MOD64i
    | 0xa7 => op_BPF_XOR64i
    | 0xb7 => op_BPF_MOV64i
    | 0xc7 => op_BPF_ARSH64i
    | _    => op_BPF_ALU64_IMM_ILLEGAL_INS
    end.

Inductive opcode_alu64_reg: Type := (**r 0xXf *)
  (** ALU64:12 *)
  | op_BPF_ADD64r
  | op_BPF_SUB64r
  | op_BPF_MUL64r
  | op_BPF_DIV64r
  | op_BPF_OR64r
  | op_BPF_AND64r
  | op_BPF_LSH64r
  | op_BPF_RSH64r
  | op_BPF_MOD64r
  | op_BPF_XOR64r
  | op_BPF_MOV64r
  | op_BPF_ARSH64r
  | op_BPF_ALU64_REG_ILLEGAL_INS.

Definition int64_to_opcode_alu64_reg (ins: int64_t): opcode_alu64_reg :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x0f => op_BPF_ADD64r
    | 0x1f => op_BPF_SUB64r
    | 0x2f => op_BPF_MUL64r
    | 0x3f => op_BPF_DIV64r
    | 0x4f => op_BPF_OR64r
    | 0x5f => op_BPF_AND64r
    | 0x6f => op_BPF_LSH64r
    | 0x7f => op_BPF_RSH64r
    | 0x9f => op_BPF_MOD64r
    | 0xaf => op_BPF_XOR64r
    | 0xbf => op_BPF_MOV64r
    | 0xcf => op_BPF_ARSH64r
    | _    => op_BPF_ALU64_REG_ILLEGAL_INS
    end.

Inductive opcode_alu32_imm: Type := (**r 0xX4 *)
  (** ALU32:13 *)
  | op_BPF_ADD32i
  | op_BPF_SUB32i
  | op_BPF_MUL32i
  | op_BPF_DIV32i
  | op_BPF_OR32i
  | op_BPF_AND32i
  | op_BPF_LSH32i
  | op_BPF_RSH32i
  | op_BPF_NEG32
  | op_BPF_MOD32i
  | op_BPF_XOR32i
  | op_BPF_MOV32i
  | op_BPF_ARSH32i
  | op_BPF_ALU32_IMM_ILLEGAL_INS.

Definition int64_to_opcode_alu32_imm (ins: int64_t): opcode_alu32_imm :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x04 => op_BPF_ADD32i
    | 0x14 => op_BPF_SUB32i
    | 0x24 => op_BPF_MUL32i
    | 0x34 => op_BPF_DIV32i
    | 0x44 => op_BPF_OR32i
    | 0x54 => op_BPF_AND32i
    | 0x64 => op_BPF_LSH32i
    | 0x74 => op_BPF_RSH32i
    | 0x84 => op_BPF_NEG32
    | 0x94 => op_BPF_MOD32i
    | 0xa4 => op_BPF_XOR32i
    | 0xb4 => op_BPF_MOV32i
    | 0xc4 => op_BPF_ARSH32i
    | _    => op_BPF_ALU32_IMM_ILLEGAL_INS
    end.

Inductive opcode_alu32_reg: Type := (**r 0xXc *)
  (** ALU32:12 *)
  | op_BPF_ADD32r
  | op_BPF_SUB32r
  | op_BPF_MUL32r
  | op_BPF_DIV32r
  | op_BPF_OR32r
  | op_BPF_AND32r
  | op_BPF_LSH32r
  | op_BPF_RSH32r
  | op_BPF_MOD32r
  | op_BPF_XOR32r
  | op_BPF_MOV32r
  | op_BPF_ARSH32r
  | op_BPF_ALU32_REG_ILLEGAL_INS.

Definition int64_to_opcode_alu32_reg (ins: int64_t): opcode_alu32_reg :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x0c => op_BPF_ADD32r
    | 0x1c => op_BPF_SUB32r
    | 0x2c => op_BPF_MUL32r
    | 0x3c => op_BPF_DIV32r
    | 0x4c => op_BPF_OR32r
    | 0x5c => op_BPF_AND32r
    | 0x6c => op_BPF_LSH32r
    | 0x7c => op_BPF_RSH32r
    | 0x9c => op_BPF_MOD32r
    | 0xac => op_BPF_XOR32r
    | 0xbc => op_BPF_MOV32r
    | 0xcc => op_BPF_ARSH32r
    | _    => op_BPF_ALU32_REG_ILLEGAL_INS
    end.

Inductive opcode_branch_imm: Type := (**r 0xX5 *)
  (**Branch: 13 *)
  | op_BPF_JA
  | op_BPF_JEQi
  | op_BPF_JGTi
  | op_BPF_JGEi
  | op_BPF_JLTi
  | op_BPF_JLEi
  | op_BPF_JSETi
  | op_BPF_JNEi
  | op_BPF_JSGTi
  | op_BPF_JSGEi
  | op_BPF_JSLTi
  | op_BPF_JSLEi
  | op_BPF_RET
  | op_BPF_JMP_IMM_ILLEGAL_INS.

Definition int64_to_opcode_branch_imm (ins: int64_t): opcode_branch_imm :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x05 => op_BPF_JA
    | 0x15 => op_BPF_JEQi
    | 0x25 => op_BPF_JGTi
    | 0x35 => op_BPF_JGEi
    | 0xa5 => op_BPF_JLTi
    | 0xb5 => op_BPF_JLEi
    | 0x45 => op_BPF_JSETi
    | 0x55 => op_BPF_JNEi
    | 0x65 => op_BPF_JSGTi
    | 0x75 => op_BPF_JSGEi
    | 0xc5 => op_BPF_JSLTi
    | 0xd5 => op_BPF_JSLEi
  (*
    | 0x85 => op_BPF_CALL*)
    | 0x95 => op_BPF_RET
    | _    => op_BPF_JMP_IMM_ILLEGAL_INS
    end.

Inductive opcode_branch_reg: Type := (**r 0xXd *)
  (**Branch: 11 *)
  | op_BPF_JEQr
  | op_BPF_JGTr
  | op_BPF_JGEr
  | op_BPF_JLTr
  | op_BPF_JLEr
  | op_BPF_JSETr
  | op_BPF_JNEr
  | op_BPF_JSGTr
  | op_BPF_JSGEr
  | op_BPF_JSLTr
  | op_BPF_JSLEr
  | op_BPF_JMP_REG_ILLEGAL_INS.

Definition int64_to_opcode_branch_reg (ins: int64_t): opcode_branch_reg :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x1d => op_BPF_JEQr
    | 0x2d => op_BPF_JGTr
    | 0x3d => op_BPF_JGEr
    | 0xad => op_BPF_JLTr
    | 0xbd => op_BPF_JLEr
    | 0x4d => op_BPF_JSETr
    | 0x5d => op_BPF_JNEr
    | 0x6d => op_BPF_JSGTr
    | 0x7d => op_BPF_JSGEr
    | 0xcd => op_BPF_JSLTr
    | 0xdd => op_BPF_JSLEr
    | _    => op_BPF_JMP_REG_ILLEGAL_INS
    end.

Inductive opcode_mem_ld_imm: Type :=  (**r 0xX8 *)
  (** Load/Store: 13 *)
  | op_BPF_LDDW
  | op_BPF_LDX_IMM_ILLEGAL_INS.

Definition int64_to_opcode_mem_ld_imm (ins: int64_t): opcode_mem_ld_imm :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x18 => op_BPF_LDDW
    | _    => op_BPF_LDX_IMM_ILLEGAL_INS
    end.

Inductive opcode_mem_ld_reg: Type :=  (**r 0xX1/0xX9 *)
  (** Load/Store: 13 *)
  | op_BPF_LDXW
  | op_BPF_LDXH
  | op_BPF_LDXB
  | op_BPF_LDXDW
  | op_BPF_LDX_REG_ILLEGAL_INS.

Definition int64_to_opcode_mem_ld_reg (ins: int64_t): opcode_mem_ld_reg :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x61 => op_BPF_LDXW
    | 0x69 => op_BPF_LDXH
    | 0x71 => op_BPF_LDXB
    | 0x79 => op_BPF_LDXDW
    | _    => op_BPF_LDX_REG_ILLEGAL_INS
    end.

Inductive opcode_mem_st_imm: Type :=  (**r 0xX2/0xXa *)
  | op_BPF_STW
  | op_BPF_STH
  | op_BPF_STB
  | op_BPF_STDW
  | op_BPF_ST_ILLEGAL_INS.

Definition int64_to_opcode_mem_st_imm (ins: int64_t): opcode_mem_st_imm :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x62 => op_BPF_STW
    | 0x6a => op_BPF_STH
    | 0x72 => op_BPF_STB
    | 0x7a => op_BPF_STDW
    | _    => op_BPF_ST_ILLEGAL_INS
    end.

Inductive opcode_mem_st_reg: Type :=  (**r 0xX3/0xXb *)
  | op_BPF_STXW
  | op_BPF_STXH
  | op_BPF_STXB
  | op_BPF_STXDW
  | op_BPF_STX_ILLEGAL_INS.

Definition int64_to_opcode_mem_st_reg (ins: int64_t): opcode_mem_st_reg :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xff) in (**r masking operation *)
    match opcode with
    | 0x63 => op_BPF_STXW
    | 0x6b => op_BPF_STXH
    | 0x73 => op_BPF_STXB
    | 0x7b => op_BPF_STXDW
    | _    => op_BPF_STX_ILLEGAL_INS
    end.

Inductive opcode: Type :=
  | op_BPF_ALU64_imm   (**r 0xX7 *)
  | op_BPF_ALU64_reg   (**r 0xXf *)
  | op_BPF_ALU32_imm   (**r 0xX4 *)
  | op_BPF_ALU32_reg   (**r 0xXc *)
  | op_BPF_Branch_imm  (**r 0xX5 *)
  | op_BPF_Branch_reg  (**r 0xXd *)
  | op_BPF_Mem_ld_imm  (**r 0xX8 *)
  | op_BPF_Mem_ld_reg  (**r 0xX1/0xX9 *)
  | op_BPF_Mem_st_imm  (**r 0xX2/0xXa *)
  | op_BPF_Mem_st_reg  (**r 0xX3/0xXb *)

  | op_BPF_ILLEGAL_INS.

Definition int64_to_opcode (ins: int64_t): opcode :=
  let opcode := Int64.unsigned (Int64.and ins int64_0xf) in (**r masking operation *)
    match opcode with
    | 0x07 => op_BPF_ALU64_imm
    | 0x0f => op_BPF_ALU64_reg
    | 0x04 => op_BPF_ALU32_imm
    | 0x0c => op_BPF_ALU32_reg
    | 0x05 => op_BPF_Branch_imm
    | 0x0d => op_BPF_Branch_reg
    | 0x08 => op_BPF_Mem_ld_imm
    | 0x01 => op_BPF_Mem_ld_reg
    | 0x09 => op_BPF_Mem_ld_reg
    | 0x02 => op_BPF_Mem_st_imm
    | 0x0a => op_BPF_Mem_st_imm
    | 0x03 => op_BPF_Mem_st_reg
    | 0x0b => op_BPF_Mem_st_reg
    | _    => op_BPF_ILLEGAL_INS
    end.
(*
Inductive opcode: Type :=
  | op_BPF_ALU64_imm : opcode_alu64_imm  -> opcode  (**r 0xX7 *)
  | op_BPF_ALU64_reg : opcode_alu64_reg  -> opcode  (**r 0xXf *)
  | op_BPF_ALU32_imm : opcode_alu32_imm  -> opcode  (**r 0xX4 *)
  | op_BPF_ALU32_reg : opcode_alu32_reg  -> opcode  (**r 0xXc *)
  | op_BPF_Branch_imm: opcode_branch_imm -> opcode  (**r 0xX5 *)
  | op_BPF_Branch_reg: opcode_branch_reg -> opcode  (**r 0xXd *)
  | op_BPF_Mem_ld_imm: opcode_mem_ld_imm -> opcode  (**r 0xX8 *)
  | op_BPF_Mem_ld_reg: opcode_mem_ld_reg -> opcode  (**r 0xX1/0xX9 *)
  | op_BPF_Mem_st_imm: opcode_mem_st_imm -> opcode  (**r 0xX2/0xXa *)
  | op_BPF_Mem_st_reg: opcode_mem_st_reg -> opcode  (**r 0xX3/0xXb *)

  | op_BPF_ILLEGAL_INS. *)


(******************** Dx related *******************)

Definition opcode_alu64_imm_eqb  (o o' : opcode_alu64_imm): bool :=
  match o , o' with
  | op_BPF_ADD64i, op_BPF_ADD64i
  | op_BPF_SUB64i, op_BPF_SUB64i
  | op_BPF_MUL64i, op_BPF_MUL64i
  | op_BPF_DIV64i, op_BPF_DIV64i
  | op_BPF_OR64i,  op_BPF_OR64i
  | op_BPF_AND64i, op_BPF_AND64i
  | op_BPF_LSH64i, op_BPF_LSH64i
  | op_BPF_RSH64i, op_BPF_RSH64i
  | op_BPF_NEG64,  op_BPF_NEG64
  | op_BPF_MOD64i, op_BPF_MOD64i
  | op_BPF_XOR64i, op_BPF_XOR64i
  | op_BPF_MOV64i, op_BPF_MOV64i
  | op_BPF_ARSH64i,op_BPF_ARSH64i
  | op_BPF_ALU64_IMM_ILLEGAL_INS, op_BPF_ALU64_IMM_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_alu64_reg_eqb  (o o' : opcode_alu64_reg): bool :=
  match o , o' with
  | op_BPF_ADD64r, op_BPF_ADD64r
  | op_BPF_SUB64r, op_BPF_SUB64r
  | op_BPF_MUL64r, op_BPF_MUL64r
  | op_BPF_DIV64r, op_BPF_DIV64r
  | op_BPF_OR64r,  op_BPF_OR64r
  | op_BPF_AND64r, op_BPF_AND64r
  | op_BPF_LSH64r, op_BPF_LSH64r
  | op_BPF_RSH64r, op_BPF_RSH64r
  | op_BPF_MOD64r, op_BPF_MOD64r
  | op_BPF_XOR64r, op_BPF_XOR64r
  | op_BPF_MOV64r, op_BPF_MOV64r
  | op_BPF_ARSH64r,op_BPF_ARSH64r
  | op_BPF_ALU64_REG_ILLEGAL_INS, op_BPF_ALU64_REG_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_alu32_imm_eqb  (o o' : opcode_alu32_imm) : bool :=
  match o , o' with
  | op_BPF_ADD32i, op_BPF_ADD32i
  | op_BPF_SUB32i, op_BPF_SUB32i
  | op_BPF_MUL32i, op_BPF_MUL32i
  | op_BPF_DIV32i, op_BPF_DIV32i
  | op_BPF_OR32i,  op_BPF_OR32i
  | op_BPF_AND32i, op_BPF_AND32i
  | op_BPF_LSH32i, op_BPF_LSH32i
  | op_BPF_RSH32i, op_BPF_RSH32i
  | op_BPF_NEG32,  op_BPF_NEG32
  | op_BPF_MOD32i, op_BPF_MOD32i
  | op_BPF_XOR32i, op_BPF_XOR32i
  | op_BPF_MOV32i, op_BPF_MOV32i
  | op_BPF_ALU32_IMM_ILLEGAL_INS, op_BPF_ALU32_IMM_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_alu32_reg_eqb  (o o' : opcode_alu32_reg) : bool :=
  match o , o' with
  | op_BPF_ADD32r, op_BPF_ADD32r
  | op_BPF_SUB32r, op_BPF_SUB32r
  | op_BPF_MUL32r, op_BPF_MUL32r
  | op_BPF_DIV32r, op_BPF_DIV32r
  | op_BPF_OR32r,  op_BPF_OR32r
  | op_BPF_AND32r, op_BPF_AND32r
  | op_BPF_LSH32r, op_BPF_LSH32r
  | op_BPF_RSH32r, op_BPF_RSH32r
  | op_BPF_MOD32r, op_BPF_MOD32r
  | op_BPF_XOR32r, op_BPF_XOR32r
  | op_BPF_MOV32r, op_BPF_MOV32r
  | op_BPF_ARSH32r,op_BPF_ARSH32r
  | op_BPF_ALU32_REG_ILLEGAL_INS, op_BPF_ALU32_REG_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_branch_imm_eqb (o o' : opcode_branch_imm): bool :=
  match o , o' with
  | op_BPF_JA,     op_BPF_JA
  | op_BPF_JEQi,   op_BPF_JEQi
  | op_BPF_JGTi,   op_BPF_JGTi
  | op_BPF_JGEi,   op_BPF_JGEi
  | op_BPF_JLTi,   op_BPF_JLTi
  | op_BPF_JLEi,   op_BPF_JLEi
  | op_BPF_JSETi,  op_BPF_JSETi
  | op_BPF_JNEi,   op_BPF_JNEi
  | op_BPF_JSGTi,  op_BPF_JSGTi
  | op_BPF_JSGEi,  op_BPF_JSGEi
  | op_BPF_JSLTi,  op_BPF_JSLTi
  | op_BPF_JSLEi,  op_BPF_JSLEi
  | op_BPF_RET,    op_BPF_RET
  | op_BPF_JMP_IMM_ILLEGAL_INS, op_BPF_JMP_IMM_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_branch_reg_eqb (o o' : opcode_branch_reg): bool :=
  match o , o' with
  | op_BPF_JEQr,   op_BPF_JEQr
  | op_BPF_JGTr,   op_BPF_JGTr
  | op_BPF_JGEr,   op_BPF_JGEr
  | op_BPF_JLTr,   op_BPF_JLTr
  | op_BPF_JLEr,   op_BPF_JLEr
  | op_BPF_JSETr,  op_BPF_JSETr
  | op_BPF_JNEr,   op_BPF_JNEr
  | op_BPF_JSGTr,  op_BPF_JSGTr
  | op_BPF_JSGEr,  op_BPF_JSGEr
  | op_BPF_JSLTr,  op_BPF_JSLTr
  | op_BPF_JSLEr,  op_BPF_JSLEr
  | op_BPF_JMP_REG_ILLEGAL_INS, op_BPF_JMP_REG_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_ld_imm_eqb (o o' : opcode_mem_ld_imm): bool :=
  match o , o' with
  | op_BPF_LDDW,   op_BPF_LDDW
  | op_BPF_LDX_IMM_ILLEGAL_INS, op_BPF_LDX_IMM_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_ld_reg_eqb (o o' : opcode_mem_ld_reg): bool :=
  match o , o' with
  | op_BPF_LDXW,   op_BPF_LDXW
  | op_BPF_LDXH,   op_BPF_LDXH
  | op_BPF_LDXB,   op_BPF_LDXB
  | op_BPF_LDXDW,  op_BPF_LDXDW
  | op_BPF_LDX_REG_ILLEGAL_INS, op_BPF_LDX_REG_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_st_imm_eqb (o o' : opcode_mem_st_imm): bool :=
  match o , o' with
  | op_BPF_STW,    op_BPF_STW
  | op_BPF_STH,    op_BPF_STH
  | op_BPF_STB,    op_BPF_STB
  | op_BPF_STDW,   op_BPF_STDW
  | op_BPF_ST_ILLEGAL_INS, op_BPF_ST_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_mem_st_reg_eqb (o o' : opcode_mem_st_reg): bool :=
  match o , o' with
  | op_BPF_STXW,   op_BPF_STXW
  | op_BPF_STXH,   op_BPF_STXH
  | op_BPF_STXB,   op_BPF_STXB
  | op_BPF_STXDW,  op_BPF_STXDW
  | op_BPF_STX_ILLEGAL_INS, op_BPF_STX_ILLEGAL_INS => true
  | _, _ => false
  end.

Definition opcode_eqb (o o' : opcode) : bool :=
  match o , o' with
  | op_BPF_ALU64_imm , op_BPF_ALU64_imm
  | op_BPF_ALU64_reg , op_BPF_ALU64_reg
  | op_BPF_ALU32_imm , op_BPF_ALU32_imm
  | op_BPF_ALU32_reg , op_BPF_ALU32_reg
  | op_BPF_Branch_imm, op_BPF_Branch_imm
  | op_BPF_Branch_reg, op_BPF_Branch_reg
  | op_BPF_Mem_ld_imm, op_BPF_Mem_ld_imm
  | op_BPF_Mem_ld_reg, op_BPF_Mem_ld_reg
  | op_BPF_Mem_st_imm, op_BPF_Mem_st_imm
  | op_BPF_Mem_st_reg, op_BPF_Mem_st_reg

  | op_BPF_ILLEGAL_INS, op_BPF_ILLEGAL_INS => true
  | _, _ => false
  end.


Definition opcode_alu64_immCompilableType :=
  MkCompilableType opcode_alu64_imm C_U8.

Definition opcode_alu64_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu64_immCompilableType  opcode_alu64_imm_eqb
    (     (op_BPF_ADD64i, 0x07)
       :: (op_BPF_SUB64i, 0x17)
       :: (op_BPF_MUL64i, 0x27)
       :: (op_BPF_DIV64i, 0x37)
       :: (op_BPF_OR64i,  0x47)
       :: (op_BPF_AND64i, 0x57)
       :: (op_BPF_LSH64i, 0x67)
       :: (op_BPF_RSH64i, 0x77)
       :: (op_BPF_NEG64,  0x87)
       :: (op_BPF_MOD64i, 0x97)
       :: (op_BPF_XOR64i, 0xa7)
       :: (op_BPF_MOV64i, 0xb7)
       :: (op_BPF_ARSH64i,0xc7):: nil)
    op_BPF_ALU64_IMM_ILLEGAL_INS
    (fun m A => opcode_alu64_imm_rect (fun _ => m A))).

Definition opcode_alu64_regCompilableType :=
  MkCompilableType opcode_alu64_reg C_U8.

Definition opcode_alu64_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu64_regCompilableType  opcode_alu64_reg_eqb
    (     (op_BPF_ADD64r, 0x0f)
       :: (op_BPF_SUB64r, 0x1f)
       :: (op_BPF_MUL64r, 0x2f)
       :: (op_BPF_DIV64r, 0x3f)
       :: (op_BPF_OR64r,  0x4f)
       :: (op_BPF_AND64r, 0x5f)
       :: (op_BPF_LSH64r, 0x6f)
       :: (op_BPF_RSH64r, 0x7f)
       :: (op_BPF_MOD64r, 0x9f)
       :: (op_BPF_XOR64r, 0xaf)
       :: (op_BPF_MOV64r, 0xbf)
       :: (op_BPF_ARSH64r,0xcf):: nil)
    op_BPF_ALU64_REG_ILLEGAL_INS
    (fun m A => opcode_alu64_reg_rect (fun _ => m A))).

Definition opcode_alu32_immCompilableType :=
  MkCompilableType opcode_alu32_imm C_U8.

Definition opcode_alu32_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu32_immCompilableType  opcode_alu32_imm_eqb
    (     (op_BPF_ADD32i, 0x04)
       :: (op_BPF_SUB32i, 0x14)
       :: (op_BPF_MUL32i, 0x24)
       :: (op_BPF_DIV32i, 0x34)
       :: (op_BPF_OR32i,  0x44)
       :: (op_BPF_AND32i, 0x54)
       :: (op_BPF_LSH32i, 0x64)
       :: (op_BPF_RSH32i, 0x74)
       :: (op_BPF_NEG32,  0x84)
       :: (op_BPF_MOD32i, 0x94)
       :: (op_BPF_XOR32i, 0xa4)
       :: (op_BPF_MOV32i, 0xb4)
       :: (op_BPF_ARSH32i,0xc4) :: nil)
    op_BPF_ALU32_IMM_ILLEGAL_INS
    (fun m A => opcode_alu32_imm_rect (fun _ => m A))).

Definition opcode_alu32_regCompilableType :=
  MkCompilableType opcode_alu32_reg C_U8.

Definition opcode_alu32_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_alu32_regCompilableType  opcode_alu32_reg_eqb
    (     (op_BPF_ADD32r, 0x0c)
       :: (op_BPF_SUB32r, 0x1c)
       :: (op_BPF_MUL32r, 0x2c)
       :: (op_BPF_DIV32r, 0x3c)
       :: (op_BPF_OR32r,  0x4c)
       :: (op_BPF_AND32r, 0x5c)
       :: (op_BPF_LSH32r, 0x6c)
       :: (op_BPF_RSH32r, 0x7c)
       :: (op_BPF_MOD32r, 0x9c)
       :: (op_BPF_XOR32r, 0xac)
       :: (op_BPF_MOV32r, 0xbc)
       :: (op_BPF_ARSH32r,0xcc) :: nil)
    op_BPF_ALU32_REG_ILLEGAL_INS
    (fun m A => opcode_alu32_reg_rect (fun _ => m A))).

Definition opcode_branch_immCompilableType :=
  MkCompilableType opcode_branch_imm C_U8.

Definition opcode_branch_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_branch_immCompilableType  opcode_branch_imm_eqb
    (     (op_BPF_JA,   0x05)
       :: (op_BPF_JEQi, 0x15)
       :: (op_BPF_JGTi, 0x25)
       :: (op_BPF_JGEi, 0x35)
       :: (op_BPF_JSETi,0x45)
       :: (op_BPF_JNEi, 0x55)
       :: (op_BPF_JSGTi,0x65)
       :: (op_BPF_JSGEi,0x75)

       :: (op_BPF_RET,  0x95)
       :: (op_BPF_JLTi, 0xa5)
       :: (op_BPF_JLEi, 0xb5)
       :: (op_BPF_JSLTi,0xc5)
       :: (op_BPF_JSLEi, 0xd5) :: nil)
    op_BPF_JMP_IMM_ILLEGAL_INS
    (fun m A => opcode_branch_imm_rect (fun _ => m A))).

Definition opcode_branch_regCompilableType :=
  MkCompilableType opcode_branch_reg C_U8.

Definition opcode_branch_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_branch_regCompilableType  opcode_branch_reg_eqb
    (     (op_BPF_JEQr, 0x1d)
       :: (op_BPF_JGTr, 0x2d)
       :: (op_BPF_JGEr, 0x3d)
       :: (op_BPF_JLTr, 0xad)
       :: (op_BPF_JLEr, 0xbd)
       :: (op_BPF_JSETr,0x4d)
       :: (op_BPF_JNEr, 0x5d)
       :: (op_BPF_JSGTr,0x6d)
       :: (op_BPF_JSGEr,0x7d)
       :: (op_BPF_JSLTr,0xcd)
       :: (op_BPF_JSLEr,0xdd) :: nil)
    op_BPF_JMP_REG_ILLEGAL_INS
    (fun m A => opcode_branch_reg_rect (fun _ => m A))).

Definition opcode_mem_ld_immCompilableType :=
  MkCompilableType opcode_mem_ld_imm C_U8.

Definition opcode_mem_ld_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_ld_immCompilableType  opcode_mem_ld_imm_eqb
    (     (op_BPF_LDDW, 0x18)
        :: nil)
    op_BPF_LDX_IMM_ILLEGAL_INS
    (fun m A => opcode_mem_ld_imm_rect (fun _ => m A))).

Definition opcode_mem_ld_regCompilableType :=
  MkCompilableType opcode_mem_ld_reg C_U8.

Definition opcode_mem_ld_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_ld_regCompilableType  opcode_mem_ld_reg_eqb
    (     (op_BPF_LDXW, 0x61)
       :: (op_BPF_LDXH, 0x69)
       :: (op_BPF_LDXB, 0x71)
       :: (op_BPF_LDXDW,0x79) :: nil)
    op_BPF_LDX_REG_ILLEGAL_INS
    (fun m A => opcode_mem_ld_reg_rect (fun _ => m A))).

Definition opcode_mem_st_immCompilableType :=
  MkCompilableType opcode_mem_st_imm C_U8.

Definition opcode_mem_st_immCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_st_immCompilableType  opcode_mem_st_imm_eqb
    (     (op_BPF_STW, 0x62)
       :: (op_BPF_STH, 0x6a)
       :: (op_BPF_STB, 0x72)
       :: (op_BPF_STDW, 0x7a) :: nil)
    op_BPF_ST_ILLEGAL_INS
    (fun m A => opcode_mem_st_imm_rect (fun _ => m A))).

Definition opcode_mem_st_regCompilableType :=
  MkCompilableType opcode_mem_st_reg C_U8.

Definition opcode_mem_st_regCompilableTypeMatchableType : MatchableType:=
  Eval compute in
 (mkEnumMatchableType
    opcode_mem_st_regCompilableType  opcode_mem_st_reg_eqb
    (     (op_BPF_STXW, 0x63)
       :: (op_BPF_STXH, 0x6b)
       :: (op_BPF_STXB, 0x73)
       :: (op_BPF_STXDW, 0x7b) :: nil)
    op_BPF_STX_ILLEGAL_INS
    (fun m A => opcode_mem_st_reg_rect (fun _ => m A))).

Definition opcodeCompilableType :=
  MkCompilableType opcode C_U8.

Definition opcodeMatchableType :=
  MkMatchableType opcodeCompilableType
    (fun x cases =>
      match cases with
      | [r0; r1; r2; r3; r4; r5; r6; r7; r8; r9; r10] =>
        Ok (Csyntax.Sswitch x
              (Csyntax.LScons (Some 0x07) r0
                (Csyntax.LScons (Some 0x0f) r1
                  (Csyntax.LScons (Some 0x04) r2
                    (Csyntax.LScons (Some 0x0c) r3
                      (Csyntax.LScons (Some 0x05) r4
                        (Csyntax.LScons (Some 0x0d) r5
                          (Csyntax.LScons (Some 0x08) r6
                            (Csyntax.LScons (Some 0x01) r7
                              (Csyntax.LScons (Some 0x09) r7
                                (Csyntax.LScons (Some 0x02) r8
                                  (Csyntax.LScons (Some 0x0a) r8
                                    (Csyntax.LScons (Some 0x03) r9
                                      (Csyntax.LScons (Some 0x0b) r9
                                        (Csyntax.LScons None r10
                                          Csyntax.LSnil))))))))))))))
            )
      | _ => Err MatchEncodingFailed
      end)
    [[]; []; []; []; []; []; []; []; []; []; []]
    [[]; []; []; []; []; []; []; []; []; []; []]
    (fun m A r whenR0 whenR1 whenR2 whenR3 whenR4 whenR5 whenR6 whenR7 whenR8 whenR9 whenR10 =>
      match r with
      | op_BPF_ALU64_imm => whenR0
      | op_BPF_ALU64_reg => whenR1
      | op_BPF_ALU32_imm => whenR2
      | op_BPF_ALU32_reg => whenR3
      | op_BPF_Branch_imm => whenR4
      | op_BPF_Branch_reg => whenR5
      | op_BPF_Mem_ld_imm => whenR6
      | op_BPF_Mem_ld_reg => whenR7
      | op_BPF_Mem_st_imm => whenR8
      | op_BPF_Mem_st_reg => whenR9
      | op_BPF_ILLEGAL_INS => whenR10
      end).

Definition int64ToopcodeSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcodeCompilableType).


Instance CINT : CType int64_t := mkCType _ (cType int64CompilableType).
Instance COP : CType opcode := mkCType _ (cType opcodeCompilableType).

Definition Const_int64_to_opcode :=
  ltac: (mkprimitive int64_to_opcode
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xf C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_alu64_immSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_alu64_immCompilableType).

Instance COP_alu64_imm : CType opcode_alu64_imm := mkCType _ (cType opcode_alu64_immCompilableType).

Definition Const_int64_to_opcode_alu64_imm :=
  ltac: (mkprimitive int64_to_opcode_alu64_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_alu64_regSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_alu64_regCompilableType).

Instance COP_alu64_reg : CType opcode_alu64_reg := mkCType _ (cType opcode_alu64_regCompilableType).

Definition Const_int64_to_opcode_alu64_reg :=
  ltac: (mkprimitive int64_to_opcode_alu64_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_alu32_immSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_alu32_immCompilableType).

Instance COP_alu32_imm : CType opcode_alu32_imm := mkCType _ (cType opcode_alu32_immCompilableType).

Definition Const_int64_to_opcode_alu32_imm :=
  ltac: (mkprimitive int64_to_opcode_alu32_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_alu32_regSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_alu32_regCompilableType).

Instance COP_alu32_reg : CType opcode_alu32_reg := mkCType _ (cType opcode_alu32_regCompilableType).

Definition Const_int64_to_opcode_alu32_reg :=
  ltac: (mkprimitive int64_to_opcode_alu32_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_branch_immSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_branch_immCompilableType).

Instance COP_opcode_branch_imm : CType opcode_branch_imm := mkCType _ (cType opcode_branch_immCompilableType).

Definition Const_int64_to_opcode_branch_imm :=
  ltac: (mkprimitive int64_to_opcode_branch_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_branch_regSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_branch_regCompilableType).

Instance COP_opcode_branch_reg : CType opcode_branch_reg := mkCType _ (cType opcode_branch_regCompilableType).

Definition Const_int64_to_opcode_branch_reg :=
  ltac: (mkprimitive int64_to_opcode_branch_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_mem_ld_immSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_mem_ld_immCompilableType).

Instance COP_opcode_mem_ld_imm : CType opcode_mem_ld_imm := mkCType _ (cType opcode_mem_ld_immCompilableType).

Definition Const_int64_to_opcode_mem_ld_imm :=
  ltac: (mkprimitive int64_to_opcode_mem_ld_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_mem_ld_regSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_mem_ld_regCompilableType).

Instance COP_opcode_mem_ld_reg : CType opcode_mem_ld_reg := mkCType _ (cType opcode_mem_ld_regCompilableType).

Definition Const_int64_to_opcode_mem_ld_reg :=
  ltac: (mkprimitive int64_to_opcode_mem_ld_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_mem_st_immSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_mem_st_immCompilableType).

Instance COP_opcode_mem_st_imm : CType opcode_mem_st_imm := mkCType _ (cType opcode_mem_st_immCompilableType).

Definition Const_int64_to_opcode_mem_st_imm :=
  ltac: (mkprimitive int64_to_opcode_mem_st_imm
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Definition int64_to_opcode_mem_st_regSymbolType :=
  MkCompilableSymbolType [int64CompilableType] (Some opcode_mem_st_regCompilableType).

Instance COP_opcode_mem_st_reg : CType opcode_mem_st_reg := mkCType _ (cType opcode_mem_st_regCompilableType).

Definition Const_int64_to_opcode_mem_st_reg :=
  ltac: (mkprimitive int64_to_opcode_mem_st_reg
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast (Csyntax.Ebinop Cop.Oand e1 C_U64_0xff C_U64) C_U8)
                           | _       => Err PrimitiveEncodingFailed
                           end)).

Close Scope Z_scope.

Module Exports.
  Definition opcode_alu64_immCompilableType  := opcode_alu64_immCompilableType.
  Definition opcode_alu64_regCompilableType  := opcode_alu64_regCompilableType.
  Definition opcode_alu32_immCompilableType  := opcode_alu32_immCompilableType.
  Definition opcode_alu32_regCompilableType  := opcode_alu32_regCompilableType.
  Definition opcode_branch_immCompilableType := opcode_branch_immCompilableType.
  Definition opcode_branch_regCompilableType := opcode_branch_regCompilableType.
  Definition opcode_mem_ld_immCompilableType := opcode_mem_ld_immCompilableType.
  Definition opcode_mem_ld_regCompilableType := opcode_mem_ld_regCompilableType.
  Definition opcode_mem_st_immCompilableType := opcode_mem_st_immCompilableType.
  Definition opcode_mem_st_regCompilableType := opcode_mem_st_regCompilableType.
  Definition opcodeMatchableType             := opcodeMatchableType.
  Definition Const_int64_to_opcode_alu64_imm := Const_int64_to_opcode_alu64_imm.
  Definition Const_int64_to_opcode_alu64_reg := Const_int64_to_opcode_alu64_reg.
  Definition Const_int64_to_opcode_alu32_imm := Const_int64_to_opcode_alu32_imm.
  Definition Const_int64_to_opcode_alu32_reg := Const_int64_to_opcode_alu32_reg.
  Definition Const_int64_to_opcode_branch_imm:= Const_int64_to_opcode_branch_imm.
  Definition Const_int64_to_opcode_branch_reg:= Const_int64_to_opcode_branch_reg.
  Definition Const_int64_to_opcode_mem_ld_imm:= Const_int64_to_opcode_mem_ld_imm.
  Definition Const_int64_to_opcode_mem_ld_reg:= Const_int64_to_opcode_mem_ld_reg.
  Definition Const_int64_to_opcode_mem_st_imm:= Const_int64_to_opcode_mem_st_imm.
  Definition Const_int64_to_opcode_mem_st_reg:= Const_int64_to_opcode_mem_st_reg.
  Definition Const_int64_to_opcode           := Const_int64_to_opcode.
End Exports.
