From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers Values AST Memory.

From dx.Type Require Import Bool Nat.

Require Import Int16 DxIntegers DxList64 DxRegs DxValues DxOpcode DxMonad DxFlag DxAST DxMemRegion DxMemType.


(**
void step(struct bpf_state* st, unsigned long long *l, unsigned long long len)
{
  

}

*)


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

Definition list_get (l: MyListType) (idx: sint32_t): M int64_t :=
  returnM (MyListIndexs32 l idx).

Definition get_mem_region (n:nat): M memory_region :=
  do mrs      <- eval_mem_regions;
  returnM (MyMemRegionsIndexnat mrs n).

Definition get_dst (ins: int64_t): M reg :=
  returnM (int64_to_dst_reg ins).

Definition reg64_to_reg32 (d: val64_t): M valu32_t := returnM (val_intuoflongu d).

Definition get_src (ins: int64_t): M reg :=
  returnM (int64_to_src_reg ins).

Definition get_offset (ins:int64_t ):M sint32_t := returnM (sint16_to_sint32 (int64_to_sint16 (Int64.shru (Int64.shl ins int64_32) int64_48))).
(** get_immediate: int64_t -> vals32_t. Tthe return type is vals32_t instead of sint32_t because `imm` is always used to be calculted with other `val` type.
  *)
(*Definition eval_offset (ins: sint32_t ):M val64_t := returnM (int64_to_vlong ins).*)

Definition get_immediate (ins:int64_t):M sint32_t := returnM (int64_to_sint32 (Int64.shru ins int64_32)).

Definition eval_immediate (ins: sint32_t): M val64_t := returnM ((Val.longofintu (sint32_to_vint ins))).

Definition get_opcode_ins (ins: int64_t): M int8_t :=
  returnM (int64_to_opcode ins).

Definition get_opcode_alu64 (op: int8_t): M opcode_alu64 :=
  returnM (byte_to_opcode_alu64 op).

Definition get_opcode_alu32 (op: int8_t): M opcode_alu32 :=
  returnM (byte_to_opcode_alu32 op).

Definition get_opcode_branch (op: int8_t): M opcode_branch :=
  returnM (byte_to_opcode_branch op).

Definition get_opcode_mem_ld_imm (op: int8_t): M opcode_mem_ld_imm :=
  returnM (byte_to_opcode_mem_ld_imm op).

Definition get_opcode_mem_ld_reg (op: int8_t): M opcode_mem_ld_reg :=
  returnM (byte_to_opcode_mem_ld_reg op).

Definition get_opcode_mem_st_imm (op: int8_t): M opcode_mem_st_imm :=
  returnM (byte_to_opcode_mem_st_imm op).

Definition get_opcode_mem_st_reg (op: int8_t): M opcode_mem_st_reg :=
  returnM (byte_to_opcode_mem_st_reg op).

Definition get_opcode (op: int8_t): M opcode :=
  returnM (byte_to_opcode op).

Definition get_addl (x y: val64_t): M val64_t := returnM (Val.addl x y).

Definition get_subl (x y: val64_t): M val64_t := returnM (Val.subl x y).

(** as I hope in C: ptr will be a `uint64 *ptr`, start_addr will be `uint64 *start_addr` and size is `uint32 *size`;
                    addr is `uint64`, chunk is `uint8`, m is `void`
                return: sint64
   The loadv/storev will run if the return value < 0, else report a memory error!!!
  *)

Definition is_well_chunk_bool (chunk: memory_chunk) : M bool :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 | Mint64 => returnM true
  | _ => returnM false
  end.


Definition check_mem_aux2 (mr: memory_region) (addr: val64_t) (chunk: memory_chunk): M val64_t :=
  do well_chunk <- is_well_chunk_bool chunk;
    if well_chunk then
      do lo_ofs <- get_subl addr (start_addr mr);
      do hi_ofs <- get_addl lo_ofs (memory_chunk_to_val64 chunk);
        if (andb (complu_le val64_zero lo_ofs) (complu_lt hi_ofs (block_size mr))) then
          if (andb (complu_le lo_ofs (memory_chunk_to_val64_upbound chunk))
                   (compl_eq val64_zero (val64_modlu lo_ofs (memory_chunk_to_val64 chunk)))) then
            returnM (Val.addl (block_ptr mr) lo_ofs) (**r > 0 *)
          else
            returnM val64_zero (**r = 0 *)
        else
          returnM val64_zero
    else
      returnM val64_zero.

Fixpoint check_mem_aux (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val64_t) {struct num}: M val64_t :=
  match num with
  | O => returnM val64_zero
  | S n =>
    do cur_mr <- get_mem_region n;
      if (perm_ge (block_perm cur_mr) perm) then
        do check_mem <- check_mem_aux2 cur_mr addr chunk;
          if compl_eq check_mem val64_zero then
            check_mem_aux n perm chunk addr
          else
            returnM check_mem
      else
        check_mem_aux n perm chunk addr
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: val64_t): M val64_t :=
  do well_chunk <- is_well_chunk_bool chunk;
    if well_chunk then
      do mem_reg_num <- eval_mem_num;
      do check_mem <- check_mem_aux mem_reg_num perm chunk addr;
        if compl_eq check_mem val64_zero then
          returnM val64_zero
        else
          returnM check_mem
    else
      returnM val64_zero.

Definition comp_and_0x08_byte (x: int8_t): M bool :=  returnM (Byte.eq int8_zero (Byte.and x int8_0x08)).

(**r pc should be u32_t *)
Definition step_opcode_alu64 (dst: reg) (dst64: val64_t) (src64: val64_t) (op: int8_t): M unit :=
  do opcode_alu64 <- get_opcode_alu64 op;
  match opcode_alu64 with
  | op_BPF_ADD64   => 
    do _ <- upd_reg dst (Val.addl    dst64 src64);
      upd_flag BPF_OK
  | op_BPF_SUB64   =>
    do _ <- upd_reg dst (Val.subl    dst64 src64);
      upd_flag BPF_OK
  | op_BPF_MUL64   =>
    do _ <- upd_reg dst (Val.mull    dst64 src64);
      upd_flag BPF_OK
  | op_BPF_DIV64   =>
    if compl_ne src64 val64_zero then
      do _ <- upd_reg dst (val64_divlu dst64 src64);
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_OR64    =>
    do _ <- upd_reg dst (Val.orl     dst64 src64);
        upd_flag BPF_OK
  | op_BPF_AND64   =>
    do _ <- upd_reg dst (Val.andl    dst64 src64);
        upd_flag BPF_OK
  | op_BPF_LSH64   =>
    do src32 <- reg64_to_reg32 src64;
    if complu_lt src64 val64_64 then
      do _ <- upd_reg dst (Val.shll    dst64 src32);
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_RSH64   =>
    do src32 <- reg64_to_reg32 src64;
    if complu_lt src64 val64_64 then
      do _ <- upd_reg dst (Val.shrlu   dst64 src32);
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_NEG64    =>
    do _ <- upd_reg dst (Val.negl    dst64);
        upd_flag BPF_OK
  | op_BPF_MOD64   =>
    do src32 <- reg64_to_reg32 src64;
    if compl_ne src64 val64_zero then
      do _ <- upd_reg dst (val64_modlu dst64 src32);
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_XOR64   =>
    do _ <- upd_reg dst (Val.xorl      dst64 src64);
        upd_flag BPF_OK
  | op_BPF_MOV64   =>
    do _ <- upd_reg dst src64;
        upd_flag BPF_OK
  | op_BPF_ARSH64  =>
    do src32 <- reg64_to_reg32 src64;
    if complu_lt src64 val64_64 then
      do _ <- upd_reg dst (Val.shrl    dst64 src32);
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_ALU64_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_alu32 (dst: reg) (dst32: valu32_t) (src32: valu32_t) (op: int8_t): M unit :=
  do opcode_alu32 <- get_opcode_alu32 op;
  match opcode_alu32 with
  | op_BPF_ADD32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.add dst32 src32));
        upd_flag BPF_OK
  | op_BPF_SUB32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.sub dst32 src32));
        upd_flag BPF_OK
  | op_BPF_MUL32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.mul dst32 src32));
        upd_flag BPF_OK
  | op_BPF_DIV32   =>
    if compl_ne_32 src32 val32_zero then
      do _ <- upd_reg dst (Val.longofintu (val32_divu dst32 src32));
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_OR32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.or  dst32 src32));
        upd_flag BPF_OK
  | op_BPF_AND32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.and dst32 src32));
        upd_flag BPF_OK
  | op_BPF_LSH32   =>
    if complu_lt_32 src32 val32_32 then
      do _ <- upd_reg dst (Val.longofintu (Val.shl dst32 src32));
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_RSH32   =>
    if complu_lt_32 src32 val32_32 then
      do _ <- upd_reg dst (Val.longofintu (Val.shru dst32 src32));
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_NEG32    =>
    do _ <- upd_reg dst (Val.longofintu (Val.neg dst32));
        upd_flag BPF_OK
  | op_BPF_MOD32   =>
    if compl_ne_32 src32 val32_zero then
      do _ <- upd_reg dst (Val.longofintu (val32_modu dst32 src32));
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_XOR32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.xor dst32 src32));
        upd_flag BPF_OK
  | op_BPF_MOV32   =>
    do _ <- upd_reg dst src32;
        upd_flag BPF_OK
  | op_BPF_ARSH32  =>
    if complu_lt_32 src32 val32_32 then
      do _ <- upd_reg dst (Val.longofintu (Val.shr dst32 src32));
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_ALU32_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

(**r ofs should be sint16_t *)
Definition step_opcode_branch (pc: sint32_t) (ofs: sint32_t) (dst64: val64_t) (src64: val64_t) (op: int8_t) : M unit :=
  do opcode_jmp <- get_opcode_branch op;
  match opcode_jmp with
  | op_BPF_JA       =>
     do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK

  | op_BPF_JEQ     =>
    if compl_eq dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JGT     =>
    if complu_gt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JGE     =>
    if complu_ge dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JLT     =>
    if complu_lt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JLE     =>
    if complu_le dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JSET     =>
    if complu_set dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JNE     =>
    if compl_ne dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JSGT     =>
    if compl_gt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JSGE     =>
    if compl_ge dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JSLT     =>
    if compl_lt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK
  | op_BPF_JSLE     =>
    if compl_le dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs);
        upd_flag BPF_OK
    else
      upd_flag BPF_OK

  | op_BPF_RET => upd_flag BPF_SUCC_RETURN
  | op_BPF_JMP_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_ld_imm (pc: sint32_t) (len: sint32_t) (dst: reg) (dst64: val64_t) (imm: sint32_t) (op: int8_t)  (l: MyListType): M unit :=
  do opcode_ld <- get_opcode_mem_ld_imm op;
  match opcode_ld with
  | op_BPF_LDDW      =>
    if (Int.lt (Int.add pc Int.one) len) then (**r pc+1 < len: pc+1 is less than the length of l *)
      do next_ins <- list_get l (Int.add pc Int.one);
      do next_imm <- get_immediate next_ins;
      do _ <- upd_reg dst (Val.or (Val.longofint (sint32_to_vint imm)) (Val.shl  (Val.longofint (sint32_to_vint next_imm)) (sint32_to_vint int32_32)));
      do _ <- upd_pc_incr;
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_LEN
  | op_BPF_LDX_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_ld_reg (pc: sint32_t) (dst: reg) (dst64: val64_t) (src64: val64_t) (op: int8_t) (ofs64: val64_t) (addr: val64_t): M unit :=
  do opcode_ld <- get_opcode_mem_ld_reg op;
  match opcode_ld with
  | op_BPF_LDXW      =>
    do check_ld <- check_mem Readable Mint32 addr;
      if compl_eq check_ld val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint32 (Val.addl src64 ofs64);
        do _ <- upd_reg dst v;
          upd_flag BPF_OK
  | op_BPF_LDXH      =>
    do check_ld <- check_mem Readable Mint16unsigned addr;
      if compl_eq check_ld val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint16unsigned (Val.addl src64 ofs64);
        do _ <- upd_reg dst v;
          upd_flag BPF_OK
  | op_BPF_LDXB      =>
    do check_ld <- check_mem Readable Mint8unsigned addr;
      if compl_eq check_ld val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint8unsigned (Val.addl src64 ofs64);
        do _ <- upd_reg dst v;
          upd_flag BPF_OK
  | op_BPF_LDXDW     =>
    do check_ld <- check_mem Readable Mint64 addr;
      if compl_eq check_ld val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint64 (Val.addl src64 ofs64);
        do _ <- upd_reg dst v;
          upd_flag BPF_OK
  | op_BPF_LDX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_imm (pc: sint32_t) (dst: reg) (dst64: val64_t) (imm: vals32_t) (op: int8_t) (ofs64: val64_t) (addr: val64_t): M unit :=
  do opcode_st <- get_opcode_mem_st_imm op;
  match opcode_st with
  | op_BPF_STW       =>
    do check_st <- check_mem Writable Mint32 addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm Mint32 (Val.addl dst64 ofs64) imm;
          upd_flag BPF_OK
  | op_BPF_STH       =>
    do check_st <- check_mem Writable Mint16unsigned addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm Mint16unsigned (Val.addl dst64 ofs64) imm;
          upd_flag BPF_OK
  | op_BPF_STB       =>
    do check_st <- check_mem Writable Mint8unsigned addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm Mint8unsigned (Val.addl dst64 ofs64) imm;
          upd_flag BPF_OK
  | op_BPF_STDW      =>
    do check_st <- check_mem Writable Mint64 addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm Mint64 (Val.addl dst64 ofs64) imm;
          upd_flag BPF_OK
  | op_BPF_ST_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_reg (pc: sint32_t) (dst: reg) (dst64: val64_t) (src64: val64_t) (op: int8_t) (ofs64: val64_t) (addr: val64_t): M unit :=
  do opcode_st <- get_opcode_mem_st_reg op;
  match opcode_st with
  | op_BPF_STXW      =>
    do check_st <- check_mem Writable Mint32 addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg Mint32 (Val.addl dst64 ofs64) src64;
          upd_flag BPF_OK
  | op_BPF_STXH      =>
    do check_st <- check_mem Writable Mint16unsigned addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg Mint16unsigned (Val.addl dst64 ofs64) src64;
          upd_flag BPF_OK
  | op_BPF_STXB      =>
    do check_st <- check_mem Writable Mint8unsigned addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg Mint8unsigned (Val.addl dst64 ofs64) src64;
          upd_flag BPF_OK
  | op_BPF_STXDW     =>
    do check_st <- check_mem Writable Mint64 addr;
      if compl_eq check_st val64_zero then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg Mint64 (Val.addl dst64 ofs64) src64;
          upd_flag BPF_OK
  | op_BPF_STX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step (len: sint32_t) (l: MyListType): M unit :=
  do pc   <- eval_pc;
  do ins  <- list_get l pc;
  do op   <- get_opcode_ins ins;
  do opc  <- get_opcode op;
  match opc with
  | op_BPF_ALU64   =>
    do dst    <- get_dst ins;
    do dst64  <- eval_reg dst;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do is_imm <- comp_and_0x08_byte op;
      if is_imm then
        do imm    <- get_immediate ins;
        do imm64  <- eval_immediate imm;
        step_opcode_alu64 dst dst64 imm64 op
      else
        do src    <- get_src ins;
        do src64  <- eval_reg src;
        step_opcode_alu64 dst dst64 src64 op                     (**r 0xX7 / 0xXf *)
  | op_BPF_ALU32   =>
    do dst    <- get_dst ins;
    do dst64  <- eval_reg dst;
    do dst32  <- reg64_to_reg32 dst64;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do is_imm <- comp_and_0x08_byte op;
      if is_imm then
        do imm    <- get_immediate ins;
        step_opcode_alu32 dst dst32 (sint32_to_vint imm) op
      else
        do src    <- get_src ins;
        do src64  <- eval_reg src;
        do src32  <- reg64_to_reg32 src64;
        step_opcode_alu32 dst dst32 src32 op                     (**r 0xX4 / 0xXc *)
  | op_BPF_Branch  =>
    do dst    <- get_dst ins;
    do dst64  <- eval_reg dst;
    do ofs    <- get_offset ins;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do is_imm <- comp_and_0x08_byte op;
      if is_imm then
        do imm    <- get_immediate ins;
        do imm64  <- eval_immediate imm;
        step_opcode_branch pc ofs dst64 imm64 op
      else
        do src    <- get_src ins;
        do src64  <- eval_reg src;
        step_opcode_branch pc ofs dst64 src64 op                    (**r 0xX5 / 0xXd *)
  | op_BPF_Mem_ld_imm  =>
    do dst    <- get_dst ins;
    do dst64  <- eval_reg dst;
    do imm    <- get_immediate ins;
    step_opcode_mem_ld_imm pc len dst dst64 imm op l                (**r 0xX8 *)
  | op_BPF_Mem_ld_reg  =>
    do dst    <- get_dst ins;
    do dst64  <- eval_reg dst;
    do src    <- get_src ins;
    do src64  <- eval_reg src;
    do ofs    <- get_offset ins;
    do ofs64  <- eval_immediate ofs;
    do addr   <- get_addl src64 ofs64;
    step_opcode_mem_ld_reg pc dst dst64 src64 op ofs64 addr       (**r 0xX1/0xX9 *)
  | op_BPF_Mem_st_imm  =>
    do dst    <- get_dst ins;
    do dst64  <- eval_reg dst;
    do ofs    <- get_offset ins;
    do ofs64  <- eval_immediate ofs;
    do imm    <- get_immediate ins;
    do addr   <- get_addl dst64 ofs64;
    step_opcode_mem_st_imm pc dst dst64 (sint32_to_vint imm) op ofs64 addr      (**r 0xX2/0xXa *)
  | op_BPF_Mem_st_reg  =>
    do dst    <- get_dst ins;
    do dst64  <- eval_reg dst;
    do src    <- get_src ins;
    do src64  <- eval_reg src;
    do ofs    <- get_offset ins;
    do ofs64  <- eval_immediate ofs;
    do addr <- get_addl dst64 ofs64;
    step_opcode_mem_st_reg pc dst dst64 src64 op ofs64 addr      (**r 0xX3/0xXb *)
  | op_BPF_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Fixpoint bpf_interpreter_aux (len: sint32_t) (fuel: nat) (l: MyListType) {struct fuel}: M unit :=
  match fuel with
  | O => upd_flag BPF_ILLEGAL_LEN
  | S fuel0 =>
    do pc <- eval_pc;
      if(andb (Int_le int32_0 pc) (Int.lt pc len)) then (**r 0 < pc < len: pc is less than the length of l *)
        do _ <- step len l;
        do _ <- upd_pc_incr;
        do f <- eval_flag;
          if flag_eq f BPF_OK then
            bpf_interpreter_aux len fuel0 l
          else
            returnM tt
      else
        upd_flag BPF_ILLEGAL_LEN
  end.

Definition bpf_interpreter (len: sint32_t) (fuel: nat) (l: MyListType): M val64_t :=
  do bpf_ctx  <- get_mem_region 0;
  do _        <- upd_reg R1 (start_addr bpf_ctx); (**r let's say the ctx memory region is also be the first one *)
  do _        <- bpf_interpreter_aux len fuel l;
  do f        <- eval_flag;
    if flag_eq f BPF_SUCC_RETURN then
      eval_reg R0
    else
      returnM val64_zero.

Close Scope monad_scope.