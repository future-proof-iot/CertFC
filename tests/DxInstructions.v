From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers Values AST Memory.

From dx.Type Require Import Bool Nat.

Require Import Int16 DxIntegers DxList64 DxRegs DxValues DxOpcode DxZ DxMonad DxPointer DxFlag.


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

Definition get_opcode (i:int64_t):M Z := returnM (Int64.unsigned (Int64.and i (Int64.repr z_0xff))).
Definition get_dst (i:int64_t):M Z := returnM (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr z_0xfff)) (Int64.repr z_8))).
Definition get_src (i:int64_t):M Z := returnM (Int64.unsigned (Int64.shru (Int64.and i (Int64.repr z_0xffff)) (Int64.repr z_12))).
Definition get_offset (i:int64_t ):M sint16_t := returnM (Int16.repr (Int64.unsigned (Int64.shru (Int64.shl i (Int64.repr z_32)) (Int64.repr z_48)))).
Definition get_immediate (i:int64_t):M vals32_t := returnM (val_intsoflongu (int64_to_vlong (Int64.shru i (Int64.repr z_32)))).

Definition list_get (l: MyListType) (idx: int64_t): M int64_t :=
  returnM (MyListIndex l idx).

Definition ins_to_opcode (ins: int64_t): M opcode :=
  do op_z <- get_opcode ins;
    returnM (z_to_opcode op_z).

Definition ins_to_dst_reg (ins: int64_t): M reg :=
  do dst_z <- get_dst ins;
    returnM (z_to_reg dst_z).

Definition ins_to_src_reg (ins: int64_t): M reg :=
  do src_z <- get_src ins;
    returnM (z_to_reg src_z).

Definition normal_return :M bpf_flag := returnM BPF_OK.

Definition ill_return :M bpf_flag := returnM BPF_ILLEGAL_INSTRUCTION.

Definition ill_len :M bpf_flag := returnM BPF_ILLEGAL_LEN.

Definition ill_div :M bpf_flag := returnM BPF_ILLEGAL_DIV.

Definition ill_shift :M bpf_flag := returnM BPF_ILLEGAL_SHIFT.

(** as I hope in C: ptr will be a `uint64 *ptr`, start_addr will be `uint64 *start_addr` and size is `uint32 *size`;
                    addr is `uint64`, chunk is `uint8`, m is `void`
                return: sint64
   The loadv/storev will run if the return value < 0, else report a memory error!!!
  *)
Axiom region_ptr: list val.
Axiom region_start_addr: list val.
Axiom region_size: list val.

Fixpoint check_mem (mem_region_num: nat) (addr: val) (chunk: memory_chunk) (m: mem): val :=
  match mem_region_num with
  | O => Vundef (**r -1 *)
  | S n => 
    let ptr_i  := List.nth mem_region_num region_ptr Vzero in
    let start_addr_i := List.nth mem_region_num region_start_addr Vzero in
    let size_i := List.nth mem_region_num region_size Vzero in
    let ofs := Val.subl addr start_addr_i in
    let hi_ofs := Val.addl ofs (Vlong (Int64.repr (size_chunk chunk))) in
      if (andb (complu_le (Vlong Int64.zero) ofs) (complu_lt hi_ofs size_i)) then
        if (andb (complu_le ofs (Vlong (Int64.repr (Int64.max_unsigned-(size_chunk chunk)))))
                 (compl_eq (Vlong (Int64.zero)) (val64_modlu ofs (Vlong (Int64.repr (align_chunk chunk)))))) then
          Val.addl ptr_i ofs (**how to translate it to `true` *)
        else
          Vundef (**r -1 *)
      else
        check_mem n addr chunk m
  end.

(** show pc < List.length l *)

Definition step (l: MyListType) (result: ptr_int64): M bpf_flag :=
  do pc <- eval_pc;
  do ins <- list_get l pc;
  do op <- ins_to_opcode ins;
  do dst <- ins_to_dst_reg ins;
  do src <- ins_to_src_reg ins;
  do dst64 <- eval_reg dst;
  do src64 <- eval_reg src;
  do ofs <- get_offset ins; (* optiomiz...**)
  do imm <- get_immediate ins;
  match op with
  (** ALU64 *)
  | op_BPF_ADD64i   =>
    do _ <- upd_reg dst (Val.addl    dst64 (Val.longofintu imm));
      normal_return
  | op_BPF_ADD64r   => 
    do _ <- upd_reg dst (Val.addl    dst64 src64);
      normal_return

  | op_BPF_SUB64i   =>
    do _ <- upd_reg dst (Val.subl    dst64 (Val.longofintu imm));
      normal_return
  | op_BPF_SUB64r   =>
    do _ <- upd_reg dst (Val.subl    dst64 src64);
      normal_return

  | op_BPF_MUL64i   =>
    do _ <- upd_reg dst (Val.mull    dst64 (Val.longofintu imm));
      normal_return
  | op_BPF_MUL64r   =>
    do _ <- upd_reg dst (Val.mull    dst64 src64);
      normal_return
  (**r how to generate exit or printf function ? *)
  | op_BPF_DIV64i   =>
    if div64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (val64_divlu dst64 (Val.longofintu imm));
        normal_return
    else
      ill_div
  | op_BPF_DIV64r   =>
    if div64_checking src64 then
      do _ <- upd_reg dst (val64_divlu dst64 src64);
        normal_return
    else
      ill_div
  | op_BPF_OR64i    =>
    do _ <- upd_reg dst (Val.orl     dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_OR64r    =>
    do _ <- upd_reg dst (Val.orl     dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_AND64i   =>
    do _ <- upd_reg dst (Val.andl    dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_AND64r   =>
    do _ <- upd_reg dst (Val.andl    dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_LSH64i   =>
    if shift64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (Val.shll    dst64 imm);
        normal_return
    else
      ill_shift
  | op_BPF_LSH64r   =>
    if shift64_checking src64 then
      do _ <- upd_reg dst (Val.shll    dst64 (val_intuoflongu src64));
        normal_return
    else
      ill_shift
  | op_BPF_RSH64i   => 
    if shift64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (Val.shrlu   dst64 imm);
        normal_return
    else
      ill_shift
  | op_BPF_RSH64r   =>
    if shift64_checking src64 then
      do _ <- upd_reg dst (Val.shrlu   dst64 (val_intuoflongu src64));
        normal_return
    else
      ill_shift
  | op_BPF_NEG64    =>
    do _ <- upd_reg dst (Val.negl    dst64);
        normal_return
  | op_BPF_MOD64i   => 
    if div64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (val64_modlu dst64 imm);
        normal_return
    else
      ill_div
  | op_BPF_MOD64r   => 
    if div64_checking src64 then
      do _ <- upd_reg dst (val64_modlu dst64 (val_intuoflongu src64));
        normal_return
    else
      ill_div
  | op_BPF_XOR64i   =>
    do _ <- upd_reg dst (Val.xorl    dst64 (Val.longofintu imm));
        normal_return
  | op_BPF_XOR64r   =>
    do _ <- upd_reg dst (Val.xorl    dst64 src64);
        normal_return
  | op_BPF_MOV64i   =>
    do _ <- upd_reg dst (Val.longofintu imm);
        normal_return
  | op_BPF_MOV64r   =>
    do _ <- upd_reg dst src64;
        normal_return
  | op_BPF_ARSH64i  => 
    if shift64_checking (Val.longofintu imm) then
      do _ <- upd_reg dst (Val.shrl    dst64  imm);
        normal_return
    else
      ill_shift
  | op_BPF_ARSH64r  => 
    if shift64_checking src64 then
      do _ <- upd_reg dst (Val.shrl    dst64  (val_intuoflongu src64));
        normal_return
    else
      ill_shift
(*ALU32*)
  | op_BPF_ADD32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_ADD32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.add (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_SUB32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_SUB32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.sub (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_MUL32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_MUL32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.mul (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_DIV32i   =>
    if div32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_div
  | op_BPF_DIV32r   =>
    if div32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (val32_divu (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_div
  | op_BPF_OR32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_OR32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.or  (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_AND32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_AND32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.and (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_LSH32i   =>
    if shift32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_shift
  | op_BPF_LSH32r   =>
    if shift32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (Val.shl (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_shift
  | op_BPF_RSH32i   =>
    if shift32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_shift
  | op_BPF_RSH32r   =>
    if shift32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (Val.shru (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_shift
  | op_BPF_NEG32    =>
    do _ <- upd_reg dst (Val.longofintu (Val.neg (val_intuoflongu (dst64))));
        normal_return
  | op_BPF_MOD32i   =>
    if div32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_div
  | op_BPF_MOD32r   =>
    if div32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (val32_modu (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_div
  | op_BPF_XOR32i   =>
    do _ <- upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) imm));
        normal_return
  | op_BPF_XOR32r   =>
    do _ <- upd_reg dst (Val.longofintu (Val.xor (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
  | op_BPF_MOV32i   =>
    do _ <- upd_reg dst imm;
        normal_return
  | op_BPF_MOV32r   =>
    do _ <- upd_reg dst (val_intuoflongu src64);
        normal_return
  | op_BPF_ARSH32i  =>
    if shift32_checking imm then
      do _ <- upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) imm));
        normal_return
    else
      ill_shift
  | op_BPF_ARSH32r  =>
    if shift32_checking (val_intuoflongu src64) then
      do _ <- upd_reg dst (Val.longofintu (Val.shr (val_intuoflongu dst64) (val_intuoflongu src64)));
        normal_return
    else
      ill_shift
  (**Branch: 23 *)
  | op_BPF_JA       =>
     do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
  | op_BPF_JEQi     =>
    if compl_eq dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JEQr     =>
    if compl_eq dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGTi     =>
    if complu_gt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGTr     =>
    if complu_gt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGEi     =>
    if complu_ge dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JGEr     =>
    if complu_ge dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLTi     =>
    if complu_lt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLTr     =>
    if complu_lt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLEi     =>
    if complu_le dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JLEr     =>
    if complu_le dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSETi     =>
    if complu_set dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSETr     =>
    if complu_set dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JNEi     =>
    if compl_ne dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JNEr     =>
    if compl_ne dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGTi     =>
    if compl_gt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGTr     =>
    if compl_gt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGEi     =>
    if compl_ge dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSGEr     =>
    if compl_ge dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLTi     =>
    if compl_lt dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLTr     =>
    if compl_lt dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLEi     =>
    if compl_le dst64 (Val.longofintu imm) then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | op_BPF_JSLEr     =>
    if compl_le dst64 src64 then
      do _ <- upd_pc (Int64.add pc (sint16_to_int64 ofs));
        normal_return
    else
      normal_return
  | _ =>  ill_return
  end.

Fixpoint bpf_interpreter (l: MyListType) (len: int64_t) (result: ptr_int64) (fuel: nat) {struct fuel}: M bpf_flag :=
  match fuel with
  | O => ill_len
  | S nfuel =>
    do pc <- eval_pc;
      if negb (Int64.ltu pc len) then (**r len <= pc: pc is over the length of l *)
        ill_len
      else
        do f <- step l result;
        do _ <- upd_pc (Int64.add pc Int64.one);
          if flag_eq f BPF_OK then
            bpf_interpreter l len result nfuel
          else
            returnM f
  end.

Close Scope monad_scope.


