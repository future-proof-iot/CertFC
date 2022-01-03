struct memory_region;
struct bpf_state;
struct memory_region {
  unsigned int *start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned int *block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned long long regsmap[11];
  struct memory_region *mrs;
  unsigned int mrs_num;
};

extern unsigned long long list_get(unsigned long long *, int);

extern struct memory_region *get_mem_region(unsigned int);

extern unsigned int get_dst(unsigned long long);

extern unsigned int reg64_to_reg32(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern int get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern unsigned long long eval_immediate(int);

extern unsigned char get_opcode_ins(unsigned long long);

extern unsigned char get_opcode_alu64(unsigned char);

extern unsigned char get_opcode_alu32(unsigned char);

extern unsigned char get_opcode_branch(unsigned char);

extern unsigned char get_opcode_mem_ld_imm(unsigned char);

extern unsigned char get_opcode_mem_ld_reg(unsigned char);

extern unsigned char get_opcode_mem_st_imm(unsigned char);

extern unsigned char get_opcode_mem_st_reg(unsigned char);

extern unsigned char get_opcode(unsigned char);

extern unsigned int get_add(unsigned int, unsigned int);

extern unsigned int get_sub(unsigned int, unsigned int);

extern unsigned int get_addr_ofs(unsigned long long, int);

extern unsigned int *get_block_ptr(struct memory_region *);

extern unsigned int get_start_addr(struct memory_region *);

extern unsigned int get_block_size(struct memory_region *);

extern unsigned int get_block_perm(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned int *check_mem_aux2(struct memory_region *, unsigned int, unsigned int);

extern unsigned int *check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned int);

extern unsigned int *check_mem(unsigned int, unsigned int, unsigned int);

extern _Bool comp_and_0x08_byte(unsigned char);

extern void step_opcode_alu64(unsigned long long, unsigned long long, unsigned int, unsigned char);

extern void step_opcode_alu32(unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_branch(unsigned long long, unsigned long long, int, int, unsigned char);

extern void step_opcode_mem_ld_imm(int, int, int, unsigned int, unsigned char, unsigned long long *);

extern void step_opcode_mem_ld_reg(unsigned int, int, unsigned int, unsigned char);

extern void step_opcode_mem_st_imm(int, unsigned int, int, unsigned int, unsigned char);

extern void step_opcode_mem_st_reg(unsigned long long, unsigned int, int, unsigned int, unsigned char);

extern void step(int, unsigned long long *);

extern void bpf_interpreter_aux(int, unsigned int, unsigned long long *);

extern unsigned long long bpf_interpreter(int, unsigned int, unsigned long long *);

extern int eval_pc(void);

extern void upd_pc(int);

extern void upd_pc_incr(void);

extern int eval_flag(void);

extern void upd_flag(int);

extern unsigned int eval_mrs_num(void);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern struct memory_region *eval_mrs_regions(void);

extern unsigned long long load_mem(unsigned int, unsigned int);

extern void store_mem_imm(unsigned int, unsigned int, int);

extern void store_mem_reg(unsigned int, unsigned int, unsigned long long);

unsigned long long list_get(unsigned long long *l, int idx)
{
  return *(l + idx);
}

struct memory_region *get_mem_region(unsigned int n)
{
  struct memory_region *mrs;
  mrs = eval_mrs_regions();
  return mrs + n;
}

unsigned int get_dst(unsigned long long ins)
{
  return (unsigned int) ((ins & 4095LLU) >> 8LLU);
}

unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

unsigned int get_src(unsigned long long ins)
{
  return (unsigned int) ((ins & 65535LLU) >> 12LLU);
}

int get_offset(unsigned long long ins)
{
  return (int) (short) (ins << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins)
{
  return (int) (ins >> 32LLU);
}

unsigned long long eval_immediate(int ins)
{
  return (unsigned long long) (unsigned int) ins;
}

unsigned char get_opcode_ins(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_branch(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode(unsigned char op)
{
  return (unsigned char) (op & 7);
}

unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}

unsigned int get_sub(unsigned int x, unsigned int y)
{
  return x - y;
}

unsigned int get_addr_ofs(unsigned long long x, int ofs)
{
  return (unsigned int) (x + (unsigned long long) ofs);
}

unsigned int *get_block_ptr(struct memory_region *mr)
{
  return (*mr).block_ptr;
}

unsigned int get_start_addr(struct memory_region *mr)
{
  return (*mr).start_addr;
}

unsigned int get_block_size(struct memory_region *mr)
{
  return (*mr).block_size;
}

unsigned int get_block_perm(struct memory_region *mr)
{
  return (*mr).block_perm;
}

_Bool is_well_chunk_bool(unsigned int chunk)
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

unsigned int *check_mem_aux2(struct memory_region *mr, unsigned int addr, unsigned int chunk)
{
  _Bool well_chunk;
  unsigned int *ptr;
  unsigned int start;
  unsigned int size;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  well_chunk = is_well_chunk_bool(chunk);
  if (well_chunk) {
    ptr = get_block_ptr(mr);
    start = get_start_addr(mr);
    size = get_block_size(mr);
    lo_ofs = get_sub(addr, start);
    hi_ofs = get_add(lo_ofs, chunk);
    if (0U <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 4294967295U - chunk && 0U == lo_ofs % chunk) {
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
}

unsigned int *check_mem_aux(unsigned int num, unsigned int perm, unsigned int chunk, unsigned int addr)
{
  unsigned int n;
  struct memory_region *cur_mr;
  unsigned int mr_perm;
  unsigned int *check_mem;
  if (num == 0U) {
    return 0;
  } else {
    n = num - 1U;
    cur_mr = get_mem_region(n);
    mr_perm = get_block_perm(cur_mr);
    if (mr_perm >= perm) {
      check_mem = check_mem_aux2(cur_mr, addr, chunk);
      if (check_mem == 0) {
        return check_mem_aux(n, perm, chunk, addr);
      } else {
        return check_mem;
      }
    } else {
      return check_mem_aux(n, perm, chunk, addr);
    }
  }
}

unsigned int *check_mem(unsigned int perm, unsigned int chunk, unsigned int addr)
{
  _Bool well_chunk;
  unsigned int mem_reg_num;
  unsigned int *check_mem;
  well_chunk = is_well_chunk_bool(chunk);
  if (well_chunk) {
    mem_reg_num = eval_mrs_num();
    check_mem = check_mem_aux(mem_reg_num, perm, chunk, addr);
    if (check_mem == 0) {
      return 0;
    } else {
      return check_mem;
    }
  } else {
    return 0;
  }
}

_Bool comp_and_0x08_byte(unsigned char x)
{
  return 0 == (x & 8);
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64, unsigned int dst, unsigned char op)
{
  unsigned char opcode_alu64;
  unsigned int src32;
  unsigned int src32;
  unsigned int src32;
  unsigned int src32;
  opcode_alu64 = get_opcode_alu64(op);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64);
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst, dst64 - src64);
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst, dst64 * src64);
      upd_flag(0);
      return;
    case 48:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 / src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64);
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst, dst64 & src64);
      upd_flag(0);
      return;
    case 96:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 << src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst, -dst64);
      upd_flag(0);
      return;
    case 144:
      src32 = reg64_to_reg32(src64);
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64);
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst, src64);
      upd_flag(0);
      return;
    case 192:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_alu32(unsigned int dst32, unsigned int src32, unsigned int dst, unsigned char op)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst,
              (unsigned long long) (unsigned int) (dst32 + src32));
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst,
              (unsigned long long) (unsigned int) (dst32 - src32));
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst,
              (unsigned long long) (unsigned int) (dst32 * src32));
      upd_flag(0);
      return;
    case 48:
      if (src32 != 0U) {
        upd_reg(dst,
                (unsigned long long) (unsigned int) (dst32 / src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst,
              (unsigned long long) (unsigned int) (dst32 | src32));
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst,
              (unsigned long long) (unsigned int) (dst32 & src32));
      upd_flag(0);
      return;
    case 96:
      if (src32 < 32U) {
        upd_reg(dst,
                (unsigned long long) (unsigned int) (dst32 << src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32 < 32U) {
        upd_reg(dst,
                (unsigned long long) (unsigned int) (dst32 >> src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst, (unsigned long long) (unsigned int) -dst32);
      upd_flag(0);
      return;
    case 144:
      if (src32 != 0U) {
        upd_reg(dst,
                (unsigned long long) (unsigned int) (dst32 % src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst,
              (unsigned long long) (unsigned int) (dst32 ^ src32));
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst, src32);
      upd_flag(0);
      return;
    case 192:
      if (src32 < 32U) {
        upd_reg(dst,
                (unsigned long long) (unsigned int) ((int) dst32
                                                      >> src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_branch(unsigned long long dst64, unsigned long long src64, int pc, int ofs, unsigned char op)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op);
  switch (opcode_jmp) {
    case 0:
      upd_pc(pc + ofs);
      upd_flag(0);
      return;
    case 16:
      if (dst64 == src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 32:
      if (dst64 > src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 48:
      if (dst64 >= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 160:
      if (dst64 < src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 176:
      if (dst64 <= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 64:
      if ((dst64 & src64) != 0LLU) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 80:
      if (dst64 != src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 96:
      if ((long long) dst64 > (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 112:
      if ((long long) dst64 >= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 192:
      if ((long long) dst64 < (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 208:
      if ((long long) dst64 <= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 144:
      upd_flag(1);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_imm(int imm, int pc, int len, unsigned int dst, unsigned char op, unsigned long long *l)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  opcode_ld = get_opcode_mem_ld_imm(op);
  switch (opcode_ld) {
    case 24:
      if (pc + 1 < len) {
        next_ins = list_get(l, pc + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst,
                (unsigned long long) imm
                  | (unsigned long long) next_imm << 32U);
        upd_pc_incr();
        upd_flag(0);
        return;
      } else {
        upd_flag(-5);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_reg(unsigned int addr, int pc, unsigned int dst, unsigned char op)
{
  unsigned char opcode_ld;
  unsigned int *addr_ptr;
  unsigned long long v;
  unsigned int *addr_ptr;
  unsigned long long v;
  unsigned int *addr_ptr;
  unsigned long long v;
  unsigned int *addr_ptr;
  unsigned long long v;
  opcode_ld = get_opcode_mem_ld_reg(op);
  switch (opcode_ld) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst, v);
        upd_flag(0);
        return;
      }
    case 105:
      addr_ptr = check_mem(1U, 2U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(2U, addr_ptr);
        upd_reg(dst, v);
        upd_flag(0);
        return;
      }
    case 113:
      addr_ptr = check_mem(1U, 1U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(1U, addr_ptr);
        upd_reg(dst, v);
        upd_flag(0);
        return;
      }
    case 121:
      addr_ptr = check_mem(1U, 8U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(8U, addr_ptr);
        upd_reg(dst, v);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm, unsigned int addr, int pc, unsigned int dst, unsigned char op)
{
  unsigned char opcode_st;
  unsigned int *addr_ptr;
  unsigned int *addr_ptr;
  unsigned int *addr_ptr;
  unsigned int *addr_ptr;
  opcode_st = get_opcode_mem_st_imm(op);
  switch (opcode_st) {
    case 98:
      addr_ptr = check_mem(2U, 4U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr, imm);
        upd_flag(0);
        return;
      }
    case 106:
      addr_ptr = check_mem(2U, 2U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr, imm);
        upd_flag(0);
        return;
      }
    case 114:
      addr_ptr = check_mem(2U, 1U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr, imm);
        upd_flag(0);
        return;
      }
    case 122:
      addr_ptr = check_mem(2U, 8U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr, imm);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64, unsigned int addr, int pc, unsigned int dst, unsigned char op)
{
  unsigned char opcode_st;
  unsigned int *addr_ptr;
  unsigned int *addr_ptr;
  unsigned int *addr_ptr;
  unsigned int *addr_ptr;
  opcode_st = get_opcode_mem_st_reg(op);
  switch (opcode_st) {
    case 99:
      addr_ptr = check_mem(2U, 4U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr, src64);
        upd_flag(0);
        return;
      }
    case 107:
      addr_ptr = check_mem(2U, 2U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr, src64);
        upd_flag(0);
        return;
      }
    case 115:
      addr_ptr = check_mem(2U, 1U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr, src64);
        upd_flag(0);
        return;
      }
    case 123:
      addr_ptr = check_mem(2U, 8U, addr);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr, src64);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(int len, unsigned long long *l)
{
  int pc;
  unsigned long long ins;
  unsigned char op;
  unsigned char opc;
  unsigned int dst;
  unsigned long long dst64;
  _Bool is_imm;
  int imm;
  unsigned long long imm64;
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
  unsigned long long imm64;
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
  pc = eval_pc();
  ins = list_get(l, pc);
  op = get_opcode_ins(ins);
  opc = get_opcode(op);
  switch (opc) {
    case 7:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        imm64 = eval_immediate(imm);
        step_opcode_alu64(dst64, imm64, dst, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(src);
        step_opcode_alu64(dst64, src64, dst, op);
        return;
      }
    case 4:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      dst32 = reg64_to_reg32(dst64);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        step_opcode_alu32(dst32, imm, dst, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(src);
        src32 = reg64_to_reg32(src64);
        step_opcode_alu32(dst32, src32, dst, op);
        return;
      }
    case 5:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      ofs = get_offset(ins);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        imm64 = eval_immediate(imm);
        step_opcode_branch(dst64, imm64, pc, ofs, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(src);
        step_opcode_branch(dst64, src64, pc, ofs, op);
        return;
      }
    case 0:
      dst = get_dst(ins);
      imm = get_immediate(ins);
      step_opcode_mem_ld_imm(imm, pc, len, dst, op,
                             l);
      return;
    case 1:
      dst = get_dst(ins);
      src = get_src(ins);
      src64 = eval_reg(src);
      ofs = get_offset(ins);
      addr = get_addr_ofs(src64, ofs);
      step_opcode_mem_ld_reg(addr, pc, dst, op);
      return;
    case 2:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      ofs = get_offset(ins);
      imm = get_immediate(ins);
      addr = get_addr_ofs(dst64, ofs);
      step_opcode_mem_st_imm(imm, addr, pc, dst, op);
      return;
    case 3:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      src = get_src(ins);
      src64 = eval_reg(src);
      ofs = get_offset(ins);
      addr = get_addr_ofs(dst64, ofs);
      step_opcode_mem_st_reg(src64, addr, pc, dst, op);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(int len, unsigned int fuel, unsigned long long *l)
{
  unsigned int fuel0;
  int pc;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    pc = eval_pc();
    if (0U <= pc && pc < len) {
      step(len, l);
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
        bpf_interpreter_aux(len, fuel0, l);
        return;
      } else {
        return;
      }
    } else {
      upd_flag(-5);
      return;
    }
  }
}

unsigned long long bpf_interpreter(int len, unsigned int fuel, unsigned long long *l)
{
  struct memory_region *bpf_ctx;
  int f;
  bpf_ctx = get_mem_region(0U);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(len, fuel, l);
  f = eval_flag();
  if (f == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


