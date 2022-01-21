
static __attribute__((always_inline)) inline struct memory_region *get_mem_region(struct bpf_state* st, unsigned int n, struct memory_region *mrs)
{
  return mrs + n;
}

static __attribute__((always_inline)) inline unsigned int get_dst(unsigned long long ins)
{
  return (unsigned int) ((ins & 4095LLU) >> 8LLU);
}

static __attribute__((always_inline)) inline unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

static __attribute__((always_inline)) inline unsigned int get_src(unsigned long long ins)
{
  return (unsigned int) ((ins & 65535LLU) >> 12LLU);
}

static __attribute__((always_inline)) inline int get_offset(unsigned long long ins)
{
  return (int) (short) (ins << 32LLU >> 48LLU);
}

static __attribute__((always_inline)) inline int get_immediate(unsigned long long ins)
{
  return (int) (ins >> 32LLU);
}

static __attribute__((always_inline)) inline long long eval_immediate(int ins)
{
  return (long long) ins;
}

static __attribute__((always_inline)) inline unsigned char get_opcode_ins(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_alu32(unsigned char op)
{
  return (unsigned char) (op & 240);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_branch(unsigned char op)
{
  return (unsigned char) (op & 240);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_mem_ld_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_mem_ld_reg(unsigned char op)
{
  return (unsigned char) (op & 255);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_mem_st_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_mem_st_reg(unsigned char op)
{
  return (unsigned char) (op & 255);
}

static __attribute__((always_inline)) inline unsigned char get_opcode(unsigned char op)
{
  return (unsigned char) (op & 7);
}

static __attribute__((always_inline)) inline unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}

static __attribute__((always_inline)) inline unsigned int get_sub(unsigned int x, unsigned int y)
{
  return x - y;
}

static __attribute__((always_inline)) inline unsigned int get_addr_ofs(unsigned long long x, int ofs)
{
  return (unsigned int) (x + (unsigned long long) ofs);
}

static __attribute__((always_inline)) inline unsigned char *get_block_ptr(struct memory_region *mr)
{
  return (*mr).block_ptr;
}

static __attribute__((always_inline)) inline unsigned int get_start_addr(struct memory_region *mr)
{
  return (*mr).start_addr;
}

static __attribute__((always_inline)) inline unsigned int get_block_size(struct memory_region *mr)
{
  return (*mr).block_size;
}

static __attribute__((always_inline)) inline unsigned int get_block_perm(struct memory_region *mr)
{
  return (*mr).block_perm;
}

static __attribute__((always_inline)) inline _Bool is_well_chunk_bool(unsigned int chunk)
{
  switch (chunk) {
    case 1:
      return 1;
    case 2:
      return 1;
    case 4:
      return 1;
    case 8:
      return 1;
    default:
      return 0;
    
  }
}

static __attribute__((always_inline)) inline unsigned char *check_mem_aux2(struct memory_region *mr, unsigned int perm, unsigned int addr, unsigned int chunk)
{
  _Bool well_chunk;
  unsigned char *ptr;
  unsigned int start;
  unsigned int size;
  unsigned int mr_perm;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  well_chunk = is_well_chunk_bool(chunk);
  if (well_chunk) {
    ptr = get_block_ptr(mr);
    start = get_start_addr(mr);
    size = get_block_size(mr);
    mr_perm = get_block_perm(mr);
    lo_ofs = get_sub(addr, start);
    hi_ofs = get_add(lo_ofs, chunk);
    if (0U <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 4294967295U - chunk && 0U == lo_ofs % chunk) {
        if (mr_perm >= perm) {
          return ptr + lo_ofs;
        } else {
          return 0;
        }
      } else {
        return 0;
      }
    } else {
      return 0;
    }
  } else {
    return 0;
  }
}

static __attribute__((always_inline)) inline unsigned char *check_mem_aux(struct bpf_state* st, unsigned int num, unsigned int perm, unsigned int chunk, unsigned int addr, struct memory_region *mrs)
{
  unsigned int n;
  struct memory_region *cur_mr;
  unsigned char *check_mem;
  if (num == 0U) {
    return 0;
  } else {
    n = num - 1U;
    cur_mr = get_mem_region(st, n, mrs);
    check_mem = check_mem_aux2(cur_mr, perm, addr, chunk);
    if (check_mem == 0) {
      return check_mem_aux(st, n, perm, chunk, addr, mrs);
    } else {
      return check_mem;
    }
  }
}

static __attribute__((always_inline)) inline unsigned char *check_mem(struct bpf_state* st, unsigned int perm, unsigned int chunk, unsigned int addr)
{
  _Bool well_chunk;
  unsigned int mem_reg_num;
  struct memory_region *mrs;
  unsigned char *check_mem;
  well_chunk = is_well_chunk_bool(chunk);
  if (well_chunk) {
    mem_reg_num = eval_mrs_num(st);
    mrs = eval_mrs_regions(st);
    check_mem =
      check_mem_aux(st, mem_reg_num, perm, chunk, addr, mrs);
    if (check_mem == 0) {
      return 0;
    } else {
      return check_mem;
    }
  } else {
    return 0;
  }
}

static __attribute__((always_inline)) inline _Bool comp_and_0x08_byte(unsigned char x)
{
  return 0 == (x & 8);
}

static __attribute__((always_inline)) inline void step_opcode_alu64(struct bpf_state* st, unsigned long long dst64, unsigned long long src64, unsigned int dst, unsigned char op)
{
  unsigned char opcode_alu64;
  unsigned int src32;
  unsigned int src32;
  unsigned int src32;
  opcode_alu64 = get_opcode_alu64(op);
  switch (opcode_alu64) {
    case 0:
      upd_reg(st, dst, dst64 + src64);
      return;
    case 16:
      upd_reg(st, dst, dst64 - src64);
      return;
    case 32:
      upd_reg(st, dst, dst64 * src64);
      return;
    case 48:
      if (src64 != 0LLU) {
        upd_reg(st, dst, dst64 / src64);
        return;
      } else {
        upd_flag(st, -9);
        return;
      }
    case 64:
      upd_reg(st, dst, dst64 | src64);
      return;
    case 80:
      upd_reg(st, dst, dst64 & src64);
      return;
    case 96:
      src32 = reg64_to_reg32(src64);
      if (src32 < 64U) {
        upd_reg(st, dst, dst64 << src32);
        return;
      } else {
        upd_flag(st, -10);
        return;
      }
    case 112:
      src32 = reg64_to_reg32(src64);
      if (src32 < 64U) {
        upd_reg(st, dst, dst64 >> src32);
        return;
      } else {
        upd_flag(st, -10);
        return;
      }
    case 128:
      if (op == 135) {
        upd_reg(st, dst, -dst64);
        return;
      } else {
        upd_flag(st, -1);
        return;
      }
    case 144:
      if (src64 != 0LLU) {
        upd_reg(st, dst, dst64 % src64);
        return;
      } else {
        upd_flag(st, -9);
        return;
      }
    case 160:
      upd_reg(st, dst, dst64 ^ src64);
      return;
    case 176:
      upd_reg(st, dst, src64);
      return;
    case 192:
      src32 = reg64_to_reg32(src64);
      if (src32 < 64U) {
        upd_reg(st, dst, (long long) dst64 >> src32);
        return;
      } else {
        upd_flag(st, -10);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void step_opcode_alu32(struct bpf_state* st, unsigned int dst32, unsigned int src32, unsigned int dst, unsigned char op)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op);
  switch (opcode_alu32) {
    case 0:
      upd_reg(st, dst, (unsigned long long) (dst32 + src32));
      return;
    case 16:
      upd_reg(st, dst, (unsigned long long) (dst32 - src32));
      return;
    case 32:
      upd_reg(st, dst, (unsigned long long) (dst32 * src32));
      return;
    case 48:
      if (src32 != 0U) {
        upd_reg(st, dst, (unsigned long long) (dst32 / src32));
        return;
      } else {
        upd_flag(st, -9);
        return;
      }
    case 64:
      upd_reg(st, dst, (unsigned long long) (dst32 | src32));
      return;
    case 80:
      upd_reg(st, dst, (unsigned long long) (dst32 & src32));
      return;
    case 96:
      if (src32 < 32U) {
        upd_reg(st, dst, (unsigned long long) (dst32 << src32));
        return;
      } else {
        upd_flag(st, -10);
        return;
      }
    case 112:
      if (src32 < 32U) {
        upd_reg(st, dst, (unsigned long long) (dst32 >> src32));
        return;
      } else {
        upd_flag(st, -10);
        return;
      }
    case 128:
      if (op == 132) {
        upd_reg(st, dst, (unsigned long long) -dst32);
        return;
      } else {
        upd_flag(st, -1);
        return;
      }
    case 144:
      if (src32 != 0U) {
        upd_reg(st, dst, (unsigned long long) (dst32 % src32));
        return;
      } else {
        upd_flag(st, -9);
        return;
      }
    case 160:
      upd_reg(st, dst, (unsigned long long) (dst32 ^ src32));
      return;
    case 176:
      upd_reg(st, dst, (unsigned long long) src32);
      return;
    case 192:
      if (src32 < 32U) {
        upd_reg(st, dst, (unsigned long long) ((int) dst32 >> src32));
        return;
      } else {
        upd_flag(st, -10);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void step_opcode_branch(struct bpf_state* st, unsigned long long dst64, unsigned long long src64, int pc, int ofs, unsigned char op)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op);
  switch (opcode_jmp) {
    case 0:
      if (op == 5) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        upd_flag(st, -1);
        return;
      }
    case 16:
      if (dst64 == src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 32:
      if (dst64 > src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 48:
      if (dst64 >= src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 160:
      if (dst64 < src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 176:
      if (dst64 <= src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 64:
      if ((dst64 & src64) != 0LLU) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 80:
      if (dst64 != src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 96:
      if ((long long) dst64 > (long long) src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 112:
      if ((long long) dst64 >= (long long) src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 192:
      if ((long long) dst64 < (long long) src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 208:
      if ((long long) dst64 <= (long long) src64) {
        upd_pc(st, pc + ofs);
        return;
      } else {
        return;
      }
    case 144:
      if (op == 149) {
        upd_flag(st, 1);
        return;
      } else {
        upd_flag(st, -1);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void step_opcode_mem_ld_imm(struct bpf_state* st, int imm, int pc, unsigned int dst, unsigned char op)
{
  int len;
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  len = eval_ins_len(st);
  opcode_ld = get_opcode_mem_ld_imm(op);
  switch (opcode_ld) {
    case 24:
      if (pc + 1 < len) {
        next_ins = eval_ins(st, pc + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(st, dst,
                (unsigned long long) imm
                  | (unsigned long long) next_imm << 32U);
        upd_pc_incr(st);
        return;
      } else {
        upd_flag(st, -5);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void step_opcode_mem_ld_reg(struct bpf_state* st, unsigned int addr, int pc, unsigned int dst, unsigned char op)
{
  unsigned char opcode_ld;
  unsigned char *addr_ptr;
  unsigned long long v;
  unsigned char *addr_ptr;
  unsigned long long v;
  unsigned char *addr_ptr;
  unsigned long long v;
  unsigned char *addr_ptr;
  unsigned long long v;
  opcode_ld = get_opcode_mem_ld_reg(op);
  switch (opcode_ld) {
    case 97:
      addr_ptr = check_mem(st, 1U, 4U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        v = load_mem(st, 4U, addr_ptr);
        upd_reg(st, dst, v);
        return;
      }
    case 105:
      addr_ptr = check_mem(st, 1U, 2U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        v = load_mem(st, 2U, addr_ptr);
        upd_reg(st, dst, v);
        return;
      }
    case 113:
      addr_ptr = check_mem(st, 1U, 1U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        v = load_mem(st, 1U, addr_ptr);
        upd_reg(st, dst, v);
        return;
      }
    case 121:
      addr_ptr = check_mem(st, 1U, 8U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        v = load_mem(st, 8U, addr_ptr);
        upd_reg(st, dst, v);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void step_opcode_mem_st_imm(struct bpf_state* st, int imm, unsigned int addr, int pc, unsigned int dst, unsigned char op)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr;
  unsigned char *addr_ptr;
  unsigned char *addr_ptr;
  unsigned char *addr_ptr;
  opcode_st = get_opcode_mem_st_imm(op);
  switch (opcode_st) {
    case 98:
      addr_ptr = check_mem(st, 2U, 4U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_imm(st, 4U, addr_ptr, imm);
        return;
      }
    case 106:
      addr_ptr = check_mem(st, 2U, 2U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_imm(st, 2U, addr_ptr, imm);
        return;
      }
    case 114:
      addr_ptr = check_mem(st, 2U, 1U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_imm(st, 1U, addr_ptr, imm);
        return;
      }
    case 122:
      addr_ptr = check_mem(st, 2U, 8U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_imm(st, 8U, addr_ptr, imm);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void step_opcode_mem_st_reg(struct bpf_state* st, unsigned long long src64, unsigned int addr, int pc, unsigned int dst, unsigned char op)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr;
  unsigned char *addr_ptr;
  unsigned char *addr_ptr;
  unsigned char *addr_ptr;
  opcode_st = get_opcode_mem_st_reg(op);
  switch (opcode_st) {
    case 99:
      addr_ptr = check_mem(st, 2U, 4U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_reg(st, 4U, addr_ptr, src64);
        return;
      }
    case 107:
      addr_ptr = check_mem(st, 2U, 2U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_reg(st, 2U, addr_ptr, src64);
        return;
      }
    case 115:
      addr_ptr = check_mem(st, 2U, 1U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_reg(st, 1U, addr_ptr, src64);
        return;
      }
    case 123:
      addr_ptr = check_mem(st, 2U, 8U, addr);
      if (addr_ptr == 0) {
        upd_flag(st, -2);
        return;
      } else {
        store_mem_reg(st, 8U, addr_ptr, src64);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void step(struct bpf_state* st)
{
  int pc;
  unsigned long long ins;
  unsigned char op;
  unsigned char opc;
  unsigned int dst;
  unsigned long long dst64;
  _Bool is_imm;
  int imm;
  long long imm64;
  unsigned int src;
  unsigned long long src64;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int dst32;
  _Bool is_imm;
  int imm;
  unsigned int src;
  unsigned long long src64;
  unsigned int src32;
  unsigned int dst;
  unsigned long long dst64;
  int ofs;
  _Bool is_imm;
  int imm;
  long long imm64;
  unsigned int src;
  unsigned long long src64;
  unsigned int dst;
  int imm;
  unsigned int dst;
  unsigned int src;
  unsigned long long src64;
  int ofs;
  unsigned int addr;
  unsigned int dst;
  unsigned long long dst64;
  int ofs;
  int imm;
  unsigned int addr;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int src;
  unsigned long long src64;
  int ofs;
  unsigned int addr;
  pc = eval_pc(st);
  ins = eval_ins(st, pc);
  op = get_opcode_ins(ins);
  opc = get_opcode(op);
  switch (opc) {
    case 7:
      dst = get_dst(ins);
      dst64 = eval_reg(st, dst);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        imm64 = eval_immediate(imm);
        step_opcode_alu64(st, dst64, imm64, dst, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(st, src);
        step_opcode_alu64(st, dst64, src64, dst, op);
        return;
      }
    case 4:
      dst = get_dst(ins);
      dst64 = eval_reg(st, dst);
      dst32 = reg64_to_reg32(dst64);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        step_opcode_alu32(st, dst32, imm, dst, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(st, src);
        src32 = reg64_to_reg32(src64);
        step_opcode_alu32(st, dst32, src32, dst, op);
        return;
      }
    case 5:
      dst = get_dst(ins);
      dst64 = eval_reg(st, dst);
      ofs = get_offset(ins);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        imm64 = eval_immediate(imm);
        step_opcode_branch(st, dst64, imm64, pc, ofs, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(st, src);
        step_opcode_branch(st, dst64, src64, pc, ofs, op);
        return;
      }
    case 0:
      dst = get_dst(ins);
      imm = get_immediate(ins);
      step_opcode_mem_ld_imm(st, imm, pc, dst, op);
      return;
    case 1:
      dst = get_dst(ins);
      src = get_src(ins);
      src64 = eval_reg(st, src);
      ofs = get_offset(ins);
      addr = get_addr_ofs(src64, ofs);
      step_opcode_mem_ld_reg(st, addr, pc, dst, op);
      return;
    case 2:
      dst = get_dst(ins);
      dst64 = eval_reg(st, dst);
      ofs = get_offset(ins);
      imm = get_immediate(ins);
      addr = get_addr_ofs(dst64, ofs);
      step_opcode_mem_st_imm(st, imm, addr, pc, dst, op);
      return;
    case 3:
      dst = get_dst(ins);
      dst64 = eval_reg(st, dst);
      src = get_src(ins);
      src64 = eval_reg(st, src);
      ofs = get_offset(ins);
      addr = get_addr_ofs(dst64, ofs);
      step_opcode_mem_st_reg(st, src64, addr, pc, dst, op);
      return;
    default:
      upd_flag(st, -1);
      return;
    
  }
}

static __attribute__((always_inline)) inline void bpf_interpreter_aux(struct bpf_state* st, unsigned int fuel)
{
  unsigned int fuel0;
  int len;
  int pc;
  int f;
  if (fuel == 0U) {
    upd_flag(st, -5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len = eval_ins_len(st);
    pc = eval_pc(st);
    if (0U <= pc && pc < len) {
      step(st); //print_bpf_state(st);
      f = eval_flag(st);
      if (f == 0) {
        upd_pc_incr(st);
        bpf_interpreter_aux(st, fuel0);
        return;
      } else {
        return;
      }
    } else {
      upd_flag(st, -5);
      return;
    }
  }
}

unsigned long long bpf_interpreter(struct bpf_state* st, unsigned int fuel)
{
  struct memory_region *mrs;
  struct memory_region *bpf_ctx;
  int f;
  mrs = eval_mrs_regions(st);
  bpf_ctx = get_mem_region(st, 0U, mrs);
  upd_reg(st, 1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(st, fuel);
  f = eval_flag(st);
  if (f == 1) {
    return eval_reg(st, 0U);
  } else {
    return 0LLU;
  }
}

