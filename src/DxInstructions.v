From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers Values AST Memory.

From dx.Type Require Import Bool Nat.

From bpf.comm Require Import MemRegion rBPFValues rBPFAST rBPFMemType Flag Regs.
From bpf.src Require Import DxIntegers DxList64 DxRegs DxValues DxOpcode DxFlag DxMemRegion DxMemType DxMonad DxNat.

From bpf.monadicmodel Require Import Opcode.

Open Scope monad_scope.

(*
Definition list_get (l: MyListType) (idx: sint32_t): M int64_t :=
  returnM (MyListIndexs32 l idx).

Definition get_mem_region (n:nat) (mrs: MyMemRegionsType): M memory_region :=
  returnM (MyMemRegionsIndexnat mrs n). *)

Definition get_dst (ins: int64_t): M reg := int64_to_dst_reg ins.

Definition reg64_to_reg32 (d: val64_t): M valu32_t := returnM (val_intuoflongu d).

Definition get_src (ins: int64_t): M reg := int64_to_src_reg ins.

Definition get_offset (ins:int64_t ):M sint32_t := returnM (get_offset ins).
(** get_immediate: int64_t -> vals32_t. Tthe return type is vals32_t instead of sint32_t because `imm` is always used to be calculted with other `val` type.
  *)
(*Definition eval_offset (ins: sint32_t ):M val64_t := returnM (int64_to_vlong ins).*)

Definition get_immediate (ins:int64_t):M sint32_t := returnM (get_immediate ins).

Definition eval_immediate (ins: sint32_t): M vals64_t := returnM ((Val_slongofint (sint32_to_vint ins))).

Definition get_src64 (x: nat8) (ins: int64_t): M val64_t :=
  if Int.eq int32_0 (Int.and (nat2int x) int32_8) then
(*
  if Nat.eqb nat8_zero (Nat.land x nat8_0x08) then *)
    do imm    <-- get_immediate ins;
    do imm64  <-- eval_immediate imm;
      returnM (Val_ulongofslong imm64)
  else
    do src    <-- get_src ins;
    do src64  <-- eval_reg src;
      returnM src64.

Definition get_src32 (x: nat8) (ins: int64_t): M valu32_t := 
  if Int.eq int32_0 (Int.and (nat2int x) int32_8) then (*
  if Nat.eqb nat8_zero (Nat.land x nat8_0x08) then *)
    do imm    <-- get_immediate ins;
      returnM (sint32_to_vint imm)
  else
    do src    <-- get_src ins;
    do src64  <-- eval_reg src;
    do src32  <-- reg64_to_reg32 src64;
      returnM src32.

Definition get_opcode_ins (ins: int64_t): M nat8 :=
  returnM (get_opcode ins).

Definition get_opcode_alu64 (op: nat8): M opcode_alu64 :=
  returnM (byte_to_opcode_alu64 op).

Definition get_opcode_alu32 (op: nat8): M opcode_alu32 :=
  returnM (byte_to_opcode_alu32 op).

Definition get_opcode_branch (op: nat8): M opcode_branch :=
  returnM (byte_to_opcode_branch op).

Definition get_opcode_mem_ld_imm (op: nat8): M opcode_mem_ld_imm :=
  returnM (byte_to_opcode_mem_ld_imm op).

Definition get_opcode_mem_ld_reg (op: nat8): M opcode_mem_ld_reg :=
  returnM (byte_to_opcode_mem_ld_reg op).

Definition get_opcode_mem_st_imm (op: nat8): M opcode_mem_st_imm :=
  returnM (byte_to_opcode_mem_st_imm op).

Definition get_opcode_mem_st_reg (op: nat8): M opcode_mem_st_reg :=
  returnM (byte_to_opcode_mem_st_reg op).

Definition get_opcode (op: nat8): M opcode :=
  returnM (byte_to_opcode op).

Definition get_add (x y: valu32_t): M valu32_t := returnM (Val.add x y).

Definition get_sub (x y: valu32_t): M valu32_t := returnM (Val.sub x y).

Definition get_addr_ofs (x: val64_t) (ofs: sint32_t): M valu32_t := returnM (val_intuoflongu (Val.addl x (Val.longofint (sint32_to_vint ofs)))).
(*
Definition get_block_ptr (mr: memory_region) : M valptr8_t := returnM (block_ptr mr). *)

Definition get_start_addr (mr: memory_region): M valu32_t := returnM (start_addr mr).

Definition get_block_size (mr: memory_region): M valu32_t := returnM (block_size mr).

Definition get_block_perm (mr: memory_region): M permission := returnM (block_perm mr).

Definition is_well_chunk_bool (chunk: memory_chunk) : M bool :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 | Mint64 => returnM true
  | _ => returnM false
  end.

Definition check_mem_aux2 (mr: memory_region) (perm: permission) (addr: valu32_t) (chunk: memory_chunk): M valptr8_t := (*
  do well_chunk <-- is_well_chunk_bool chunk;
    if well_chunk then *) (*
      do ptr    <-- get_block_ptr mr; (**r Vptr b 0 *)*)
  do start  <-- get_start_addr mr;
  do size   <-- get_block_size mr;
  do mr_perm  <-- get_block_perm mr;
  do lo_ofs <-- get_sub addr start;
  do hi_ofs <-- get_add lo_ofs (memory_chunk_to_valu32 chunk);
    if andb (andb
              (compu_lt_32 hi_ofs size)
              (andb (compu_le_32 lo_ofs (memory_chunk_to_valu32_upbound chunk))
                    (comp_eq_32 val32_zero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
            (perm_ge mr_perm perm) then
      returnM (Val.add (block_ptr mr) lo_ofs) (**r Vptr b lo_ofs *)
    else
      returnM valptr_null (**r = 0 *). (*
    else
      returnM valptr_null.*)

Fixpoint check_mem_aux (num: nat) (perm: permission) (chunk: memory_chunk) (addr: valu32_t) (mrs: MyMemRegionsType) {struct num}: M valptr8_t :=
  match num with
  | O => returnM valptr_null
  | S n =>
    do cur_mr    <-- get_mem_region n mrs;
    do check_mem <-- check_mem_aux2 cur_mr perm addr chunk;
    do is_null   <-- cmp_ptr32_nullM check_mem;
      if is_null then
        check_mem_aux n perm chunk addr mrs
      else
        returnM check_mem
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: valu32_t): M valptr8_t :=
  do well_chunk <-- is_well_chunk_bool chunk;
    if well_chunk then
      do mem_reg_num <-- eval_mrs_num;
      do mrs         <-- eval_mrs_regions;
      do check_mem   <-- check_mem_aux mem_reg_num perm chunk addr mrs;
      do is_null     <-- cmp_ptr32_nullM check_mem;
        if is_null then
          returnM valptr_null
        else
          returnM check_mem
    else
      returnM valptr_null.

(**r pc should be u32_t *)
Definition step_opcode_alu64 (dst64: val64_t) (src64: val64_t) (dst: reg) (op: nat8): M unit :=
  do opcode_alu64 <-- get_opcode_alu64 op;
  match opcode_alu64 with
  | op_BPF_ADD64   => 
    do _ <-- upd_reg dst (Val.addl    dst64 src64); returnM tt
  | op_BPF_SUB64   =>
    do _ <-- upd_reg dst (Val.subl    dst64 src64); returnM tt
  | op_BPF_MUL64   =>
    do _ <-- upd_reg dst (Val.mull    dst64 src64); returnM tt
  | op_BPF_DIV64   =>
    if compl_ne src64 val64_zero then
      do _ <-- upd_reg dst (val64_divlu dst64 src64); returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_DIV; returnM tt (**r we do it for the clightproof , we could omit it later *)
  | op_BPF_OR64    =>
    do _ <-- upd_reg dst (Val.orl     dst64 src64); returnM tt
  | op_BPF_AND64   =>
    do _ <-- upd_reg dst (Val.andl    dst64 src64); returnM tt
  | op_BPF_LSH64   =>
    do src32 <-- reg64_to_reg32 src64;
    if compu_lt_32 src32 val32_64 then
      do _ <-- upd_reg dst (Val.shll    dst64 src32); returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_SHIFT; returnM tt
  | op_BPF_RSH64   =>
    do src32 <-- reg64_to_reg32 src64;
    if compu_lt_32 src32 val32_64 then
      do _ <-- upd_reg dst (Val.shrlu   dst64 src32); returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_SHIFT; returnM tt
  | op_BPF_NEG64    =>
    if Nat.eqb op nat8_0x87 then
      do _ <-- upd_reg dst (Val.negl    dst64); returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_MOD64   =>
    if compl_ne src64 val64_zero then
      do _ <-- upd_reg dst (val64_modlu dst64 src64); returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_DIV; returnM tt
  | op_BPF_XOR64   =>
    do _ <-- upd_reg dst (Val.xorl      dst64 src64); returnM tt
  | op_BPF_MOV64   =>
    do _ <-- upd_reg dst src64; returnM tt
  | op_BPF_ARSH64  =>
    do src32 <-- reg64_to_reg32 src64;
    if compu_lt_32 src32 val32_64 then
      do _ <-- upd_reg dst (Val.shrl    dst64 src32); returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_SHIFT; returnM tt
  | op_BPF_ALU64_ILLEGAL_INS => do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  end.

Definition step_opcode_alu32 (dst32: valu32_t) (src32: valu32_t) (dst: reg) (op: nat8): M unit :=
  do opcode_alu32 <-- get_opcode_alu32 op;
  match opcode_alu32 with
  | op_BPF_ADD32   =>
    do _ <-- upd_reg dst (Val.longofintu (Val.add dst32 src32)); returnM tt
  | op_BPF_SUB32   =>
    do _ <-- upd_reg dst (Val.longofintu (Val.sub dst32 src32)); returnM tt
  | op_BPF_MUL32   =>
    do _ <-- upd_reg dst (Val.longofintu (Val.mul dst32 src32)); returnM tt
  | op_BPF_DIV32   =>
    if comp_ne_32 src32 val32_zero then
      do _ <-- upd_reg dst (Val.longofintu (val32_divu dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_OR32   =>
    do _ <-- upd_reg dst (Val.longofintu (Val.or  dst32 src32)); returnM tt
  | op_BPF_AND32   =>
    do _ <-- upd_reg dst (Val.longofintu (Val.and dst32 src32)); returnM tt
  | op_BPF_LSH32   =>
    if compu_lt_32 src32 val32_32 then
      do _ <-- upd_reg dst (Val.longofintu (Val.shl dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_RSH32   =>
    if compu_lt_32 src32 val32_32 then
      do _ <-- upd_reg dst (Val.longofintu (Val.shru dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_NEG32    =>
    if Nat.eqb op nat8_0x84 then
      do _ <-- upd_reg dst (Val.longofintu (Val.neg dst32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_INSTRUCTION
  | op_BPF_MOD32   =>
    if comp_ne_32 src32 val32_zero then
      do _ <-- upd_reg dst (Val.longofintu (val32_modu dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_XOR32   =>
    do _ <-- upd_reg dst (Val.longofintu (Val.xor dst32 src32)); returnM tt
  | op_BPF_MOV32   =>
    do _ <-- upd_reg dst (Val.longofintu src32); returnM tt
  | op_BPF_ARSH32  =>
    if compu_lt_32 src32 val32_32 then
      do _ <-- upd_reg dst (Val.longofint (Val.shr dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_ALU32_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

(**r ofs should be sint16_t *)
Definition step_opcode_branch (dst64: val64_t) (src64: val64_t) (pc: uint32_t) (ofs: uint32_t) (op: nat8) : M unit :=
  do opcode_jmp <-- get_opcode_branch op;
  match opcode_jmp with
  | op_BPF_JA       =>
    if Nat.eqb op nat8_0x05 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_JEQ     =>
    if compl_eq dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JGT     =>
    if complu_gt dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JGE     =>
    if complu_ge dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JLT     =>
    if complu_lt dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JLE     =>
    if complu_le dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSET     =>
    if complu_set dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JNE     =>
    if compl_ne dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSGT     =>
    if compl_gt dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSGE     =>
    if compl_ge dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSLT     =>
    if compl_lt dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSLE     =>
    if compl_le dst64 src64 then
      do _ <-- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt

  | op_BPF_CALL =>
    if Nat.eqb op nat8_0x85 then
      do f_ptr    <-- _bpf_get_call (val_intsoflongu src64);
      do is_null  <-- cmp_ptr32_nullM f_ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_CALL
        else
          do res  <-- exec_function f_ptr;
            upd_reg R0 (Val.longofintu res)
    else
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt

  | op_BPF_RET => 
    if Nat.eqb op nat8_0x95 then
      do _ <-- upd_flag BPF_SUCC_RETURN; returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_JMP_ILLEGAL_INS =>
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  end.

Definition step_opcode_mem_ld_imm (imm: sint32_t) (pc: uint32_t) (dst: reg) (op: nat8): M unit :=
  do len  <-- eval_ins_len;
  do opcode_ld <-- get_opcode_mem_ld_imm op;
  match opcode_ld with
  | op_BPF_LDDW      =>
    if (Int.ltu (Int.add pc int32_1) len) then (**r pc+1 < len: pc+1 is less than the length of l *)
      do next_ins <-- eval_ins (Int.add pc int32_1);
      do next_imm <-- get_immediate next_ins;
      do _ <-- upd_reg dst (Val.orl (Val.longofint (sint32_to_vint imm)) (Val.shll  (Val.longofint (sint32_to_vint next_imm)) (sint32_to_vint int32_32)));
      do _ <-- upd_pc_incr; returnM tt
    else
      upd_flag BPF_ILLEGAL_LEN
  | op_BPF_LDX_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.


Definition step_opcode_mem_ld_reg (addr: valu32_t) (pc: uint32_t) (dst: reg) (op: nat8): M unit :=
  do opcode_ld <-- get_opcode_mem_ld_reg op;
  match opcode_ld with
  | op_BPF_LDXW      =>
    do addr_ptr <-- check_mem Readable Mint32 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <-- load_mem Mint32 addr_ptr;
        do _ <-- upd_reg dst v; returnM tt
  | op_BPF_LDXH      =>
    do addr_ptr <-- check_mem Readable Mint16unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <-- load_mem Mint16unsigned addr_ptr;
        do _ <-- upd_reg dst v; returnM tt
  | op_BPF_LDXB      =>
    do addr_ptr <-- check_mem Readable Mint8unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <-- load_mem Mint8unsigned addr_ptr;
        do _ <-- upd_reg dst v; returnM tt
  | op_BPF_LDXDW     =>
    do addr_ptr <-- check_mem Readable Mint64 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <-- load_mem Mint64 addr_ptr;
        do _ <-- upd_reg dst v; returnM tt
  | op_BPF_LDX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_imm (imm: vals32_t) (addr: valu32_t) (pc: uint32_t) (dst: reg) (op: nat8): M unit :=
  do opcode_st <-- get_opcode_mem_st_imm op;
  match opcode_st with
  | op_BPF_STW       =>
    do addr_ptr <-- check_mem Writable Mint32 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_imm addr_ptr Mint32 imm; returnM tt
  | op_BPF_STH       =>
    do addr_ptr <-- check_mem Writable Mint16unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_imm addr_ptr Mint16unsigned imm; returnM tt
  | op_BPF_STB       =>
    do addr_ptr <-- check_mem Writable Mint8unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_imm addr_ptr Mint8unsigned imm; returnM tt
  | op_BPF_STDW      =>
    do addr_ptr <-- check_mem Writable Mint64 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_imm addr_ptr Mint64 imm; returnM tt
  | op_BPF_ST_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_reg (src64: val64_t) (addr: valu32_t) (pc: uint32_t) (dst: reg) (op: nat8): M unit :=
  do opcode_st <-- get_opcode_mem_st_reg op;
  match opcode_st with
  | op_BPF_STXW      =>
    do addr_ptr <-- check_mem Writable Mint32 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_reg addr_ptr Mint32 src64; returnM tt
  | op_BPF_STXH      =>
    do addr_ptr <-- check_mem Writable Mint16unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_reg addr_ptr Mint16unsigned src64; returnM tt
  | op_BPF_STXB      =>
    do addr_ptr <-- check_mem Writable Mint8unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_reg addr_ptr Mint8unsigned src64; returnM tt
  | op_BPF_STXDW     =>
    do addr_ptr <-- check_mem Writable Mint64 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem_reg addr_ptr Mint64 src64; returnM tt
  | op_BPF_STX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step: M unit :=
  do pc   <-- eval_pc;
  do ins  <-- eval_ins pc;
  do op   <-- get_opcode_ins ins;
  do opc  <-- get_opcode op;
  do dst  <-- get_dst ins;
  match opc with
  | op_BPF_ALU64   =>
    do dst64  <-- eval_reg dst;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do src64  <-- get_src64 op ins;
      step_opcode_alu64 dst64 src64 dst op                     (**r 0xX7 / 0xXf *)
  | op_BPF_ALU32   =>
    do dst64  <-- eval_reg dst;
    do dst32  <-- reg64_to_reg32 dst64;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do src32  <-- get_src32 op ins;
      step_opcode_alu32 dst32 src32 dst op                     (**r 0xX4 / 0xXc *)
  | op_BPF_Branch  =>
    do dst64  <-- eval_reg dst;
    do ofs    <-- get_offset ins;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do src64  <-- get_src64 op ins;
      step_opcode_branch dst64 src64 pc (sint32_to_uint32 ofs) op                    (**r 0xX5 / 0xXd *)
  | op_BPF_Mem_ld_imm  =>
    do imm    <-- get_immediate ins;
      step_opcode_mem_ld_imm imm pc dst op              (**r 0xX8 *)
  | op_BPF_Mem_ld_reg  =>
    do src    <-- get_src ins;
    do src64  <-- eval_reg src;
    do ofs    <-- get_offset ins;
    do addr   <-- get_addr_ofs src64 ofs;
      step_opcode_mem_ld_reg addr pc dst op       (**r 0xX1/0xX9 *)
  | op_BPF_Mem_st_imm  =>
    do dst64  <-- eval_reg dst;
    do ofs    <-- get_offset ins;
    do imm    <-- get_immediate ins;
    do addr   <-- get_addr_ofs dst64 ofs;
      step_opcode_mem_st_imm (sint32_to_vint imm) addr pc dst op       (**r 0xX2/0xXa *)
  | op_BPF_Mem_st_reg  =>
    do dst64  <-- eval_reg dst;
    do src    <-- get_src ins;
    do src64  <-- eval_reg src;
    do ofs    <-- get_offset ins;
    do addr   <-- get_addr_ofs dst64 ofs;
      step_opcode_mem_st_reg src64 addr pc dst op       (**r 0xX3/0xXb *)
  | op_BPF_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Fixpoint bpf_interpreter_aux (fuel: nat) {struct fuel}: M unit :=
  match fuel with
  | O => upd_flag BPF_ILLEGAL_LEN
  | S fuel0 =>
    do len  <-- eval_ins_len;
    do pc   <-- eval_pc;
      if (Int.ltu pc len) then (**r 0 < pc < len: pc is less than the length of l *)
        do _ <-- step;
        do f <-- eval_flag;
          if flag_eq f BPF_OK then
            do len0  <-- eval_ins_len;
            do pc0   <-- eval_pc;
              if (Int.ltu (Int.add pc0 int32_1) len0) then
                do _ <-- upd_pc_incr;
                  bpf_interpreter_aux fuel0
              else
                upd_flag BPF_ILLEGAL_LEN
          else
            returnM tt
      else
        upd_flag BPF_ILLEGAL_LEN
  end.

Definition bpf_interpreter (fuel: nat): M val64_t :=
  do mrs      <-- eval_mrs_regions;
  do bpf_ctx  <-- get_mem_region 0 mrs;
  do start  <-- get_start_addr bpf_ctx;
  do _        <-- upd_reg R1 (Val.longofintu start); (**r let's say the ctx memory region is also be the first one *)
  do _        <-- bpf_interpreter_aux fuel;
  do f        <-- eval_flag;
    if flag_eq f BPF_SUCC_RETURN then
      do res  <-- eval_reg R0;
        returnM res
    else
      returnM val64_zero.

Close Scope monad_scope.