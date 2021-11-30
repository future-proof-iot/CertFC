#include "interpreter.h"

#include <inttypes.h>
#include<stdlib.h>
#include<stddef.h>


void print_bpf_state(struct bpf_state* st){
  printf("pc= %" PRIu64 "\n", (uint64_t) (*st).state_pc);
  printf("flag= %d\n", (*st).bpf_flag);
  for(int i = 0; i < 11; i++){
    printf("R%d",i);
    printf("= %" PRIu64 ";", (uint64_t) (*st).regsmap[i]);
  }
  printf("\n");
}


static unsigned long long eval_pc (struct bpf_state* st) {
  return (*st).state_pc;
}


static void upd_pc(unsigned long long pc, struct bpf_state* st) {
  (*st).state_pc = pc;
  return ;
}
static void upd_pc_incr(struct bpf_state* st) {
  (*st).state_pc = (*st).state_pc+1;
  return ;
}


static unsigned long long eval_reg(unsigned int i, struct bpf_state* st){
  if (i < 11){
    return (*st).regsmap[i];
  }
  else {
    (*st).bpf_flag = BPF_ILLEGAL_REGISTER;
    return 0; //if here we update the bpf_flag, we must check bpf_flag after eval_reg
  }
}

static void upd_reg (unsigned int i, unsigned long long v, struct bpf_state* st){
  if (i < 11){
    (*st).regsmap[i] = v;
  }
  else {
    (*st).bpf_flag = BPF_ILLEGAL_REGISTER;
  }
  return ; //if here we update the bpf_flag, we must check bpf_flag after eval_reg
}

static int eval_flag(struct bpf_state* st){
  return (*st).bpf_flag;
}

static void upd_flag(int f, struct bpf_state* st){
  (*st).bpf_flag = f;
  return ;
}

static unsigned long long load_mem(unsigned int chunk, unsigned long long v, struct bpf_state* st){
  switch (chunk) {
    case 1: return *(unsigned char *) (intptr_t)v;
    case 2: return *(unsigned short *) (intptr_t)v;
    case 4: return *(unsigned int *) (intptr_t)v;
    case 8: return *(unsigned long long *) (intptr_t) v;
    default: /*printf ("load:addr = %" PRIu64 "\n", v);*/ (*st).bpf_flag = BPF_ILLEGAL_MEM; return 0;
  }
}

static void store_mem_reg(unsigned int chunk, unsigned long long addr, unsigned long long v, struct bpf_state* st){
  switch (chunk) {
    case 1: *(unsigned char *) (intptr_t) addr = v; return ;
    case 2: *(unsigned short *) (intptr_t) addr = v; return ;
    case 4: *(unsigned int *) (intptr_t) addr = v; return ;
    case 8: *(unsigned long long *) (intptr_t) addr = v; return ;
    default: /*printf ("store_reg:addr = %" PRIu64 "\n", addr);*/ (*st).bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
}

static void store_mem_imm(unsigned int chunk, unsigned long long addr, int v, struct bpf_state* st){
  switch (chunk) {
    case 1: *(unsigned char *) addr = v; return ;
    case 2: *(unsigned short *) addr = v; return ;
    case 4: *(unsigned int *) addr = v; return ;
    case 8: *(unsigned long long *) addr = v; return ;
    default: /*printf ("store_imm:addr = %" PRIu64 "\n", addr);*/ (*st).bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
}

/*******************automatically generated by dx ***************************/

static unsigned long long list_get(unsigned long long *l, unsigned long long idx0)
{
  return *(l + idx0);
}

static unsigned char get_opcode(unsigned long long ins0)
{
  return (unsigned char) (ins0 & 255LLU);
}

static unsigned int get_dst(unsigned long long ins1)
{
  return (unsigned int) ((ins1 & 4095LLU) >> 8LLU);
}

static unsigned int get_src(unsigned long long ins2)
{
  return (unsigned int) ((ins2 & 65535LLU) >> 12LLU);
}

static short get_offset(unsigned long long i0)
{
  return (short) (i0 << 32LLU >> 48LLU);
}

static int get_immediate(unsigned long long i1)
{
  return (int) (i1 >> 32LLU);
}

static unsigned long long get_addl(unsigned long long x, unsigned long long y)
{
  return x + y;
}

static unsigned long long get_subl(unsigned long long x1, unsigned long long y1)
{
  return x1 - y1;
}

static unsigned long long getMemRegion_block_ptr(struct memory_region *mr0)
{
  return 1LLU;
}

static unsigned long long getMemRegion_start_addr(struct memory_region *mr1)
{
  return (*mr1).start_addr;
}

static unsigned long long getMemRegion_block_size(struct memory_region *mr2)
{
  return (*mr2).block_size;
}

static _Bool is_well_chunk_bool(unsigned int chunk0)
{
  switch (chunk0) {
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

static unsigned long long check_mem_aux(struct memory_region *mr3, unsigned long long addr0, unsigned int chunk1)
{
  _Bool well_chunk;
  unsigned long long ptr;
  unsigned long long start;
  unsigned long long size;
  unsigned long long lo_ofs;
  unsigned long long hi_ofs;
  well_chunk = is_well_chunk_bool(chunk1);
  if (well_chunk) {
    ptr = getMemRegion_block_ptr(mr3);
    start = getMemRegion_start_addr(mr3);
    size = getMemRegion_block_size(mr3);
    lo_ofs = get_subl(addr0, start);
    hi_ofs = get_addl(lo_ofs, chunk1);
    if (0LLU <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 18446744073709551615LLU - chunk1
            && 0LLU == lo_ofs % chunk1) {
        return ptr + lo_ofs;
      } else {
        return 0LLU;
      }
    } else {
      return 0LLU;
    }
  } else {
    return 0LLU;
  }
}

static unsigned long long check_mem(struct memory_regions *mrs4, unsigned long long addr1, unsigned int chunk2)
{
  unsigned long long check_mem_ctx;
  unsigned long long check_mem_stk;
  unsigned long long check_mem_content;
  check_mem_ctx = check_mem_aux((*mrs4).bpf_ctx, addr1, chunk2);
  if (check_mem_ctx == 0LLU) {
    check_mem_stk = check_mem_aux((*mrs4).bpf_stk, addr1, chunk2);
    if (check_mem_stk == 0LLU) {
      check_mem_content = check_mem_aux((*mrs4).content, addr1, chunk2);
      if (check_mem_content == 0LLU) {
        return 0LLU;
      } else {
        return check_mem_content;
      }
    } else {
      return check_mem_stk;
    }
  } else {
    return check_mem_ctx;
  }
}

void step(unsigned long long *l0, unsigned long long len0, struct bpf_state* st)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned char op;
  unsigned int dst;
  unsigned int src;
  unsigned long long dst64;
  unsigned long long src64;
  short ofs;
  int imm;
  unsigned long long addr_dst;
  unsigned long long addr_src;
  unsigned long long next_ins;
  int next_imm;
  unsigned long long check_ldxw;
  unsigned long long v_xw;
  unsigned long long check_ldxh;
  unsigned long long v_xh;
  unsigned long long check_ldxb;
  unsigned long long v_xb;
  unsigned long long check_ldxdw;
  unsigned long long v_xdw;
  unsigned long long check_stw;
  unsigned long long check_sth;
  unsigned long long check_stb;
  unsigned long long check_stdw;
  unsigned long long check_stxw;
  unsigned long long check_stxh;
  unsigned long long check_stxb;
  unsigned long long check_stxdw;
  pc = eval_pc(st);
  ins = list_get(l0, pc);
  op = get_opcode(ins);
  dst = get_dst(ins);
  src = get_src(ins);
  dst64 = eval_reg(dst, st);
  src64 = eval_reg(src, st);
  ofs = get_offset(ins);
  imm = get_immediate(ins);
  addr_dst = get_addl(dst64, ofs);
  addr_src = get_addl(src64, ofs);
  switch (op) {
    case 7:
      upd_reg(dst, dst64 + (unsigned long long) imm, st);
      upd_flag(0, st);
      return;
    case 15:
      upd_reg(dst, dst64 + src64, st);
      upd_flag(0, st);
      return;
    case 23:
      upd_reg(dst, dst64 - (unsigned long long) imm, st);
      upd_flag(0, st);
      return;
    case 31:
      upd_reg(dst, dst64 - src64, st);
      upd_flag(0, st);
      return;
    case 39:
      upd_reg(dst, dst64 * (unsigned long long) imm, st);
      upd_flag(0, st);
      return;
    case 47:
      upd_reg(dst, dst64 * src64, st);
      upd_flag(0, st);
      return;
    case 55:
      if ((unsigned long long) imm != 0LLU) {
        upd_reg(dst, dst64 / (unsigned long long) imm, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 63:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 / src64, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 71:
      upd_reg(dst, dst64 | (unsigned long long) imm, st);
      upd_flag(0, st);
      return;
    case 79:
      upd_reg(dst, dst64 | src64, st);
      upd_flag(0, st);
      return;
    case 87:
      upd_reg(dst, dst64 & (unsigned long long) imm, st);
      upd_flag(0, st);
      return;
    case 95:
      upd_reg(dst, dst64 & src64, st);
      upd_flag(0, st);
      return;
    case 103:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, dst64 << imm, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 111:
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 << (unsigned int) src64, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 119:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, dst64 >> imm, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 127:
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> (unsigned int) src64, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 135:
      upd_reg(dst, -dst64, st);
      upd_flag(0, st);
      return;
    case 151:
      if ((unsigned long long) imm != 0LLU) {
        upd_reg(dst, dst64 % imm, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 159:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % (unsigned int) src64, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 167:
      upd_reg(dst, dst64 ^ (unsigned long long) imm, st);
      upd_flag(0, st);
      return;
    case 175:
      upd_reg(dst, dst64 ^ src64, st);
      upd_flag(0, st);
      return;
    case 183:
      upd_reg(dst, (unsigned long long) imm, st);
      upd_flag(0, st);
      return;
    case 191:
      upd_reg(dst, src64, st);
      upd_flag(0, st);
      return;
    case 199:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, (long long) dst64 >> imm, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 207:
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> (unsigned int) src64, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 4:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 + imm), st);
      upd_flag(0, st);
      return;
    case 12:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     + (unsigned int) src64), st);
      upd_flag(0, st);
      return;
    case 20:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 - imm), st);
      upd_flag(0, st);
      return;
    case 28:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     - (unsigned int) src64), st);
      upd_flag(0, st);
      return;
    case 36:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 * imm), st);
      upd_flag(0, st);
      return;
    case 44:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     * (unsigned int) src64), st);
      upd_flag(0, st);
      return;
    case 52:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 / imm), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 60:
      if ((unsigned int) src64 != 0U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       / (unsigned int) src64), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 68:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 | imm), st);
      upd_flag(0, st);
      return;
    case 76:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     | (unsigned int) src64), st);
      upd_flag(0, st);
      return;
    case 84:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 & imm), st);
      upd_flag(0, st);
      return;
    case 92:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     & (unsigned int) src64), st);
      upd_flag(0, st);
      return;
    case 100:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 << imm), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 108:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       << (unsigned int) src64), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 116:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 >> imm), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 124:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       >> (unsigned int) src64), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 132:
      upd_reg(dst, (unsigned long long) -((unsigned int) dst64), st);
      upd_flag(0, st);
      return;
    case 148:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 % imm), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 156:
      if ((unsigned int) src64 != 0U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       % (unsigned int) src64), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-9, st);
        return;
      }
    case 164:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 ^ imm), st);
      upd_flag(0, st);
      return;
    case 172:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     ^ (unsigned int) src64), st);
      upd_flag(0, st);
      return;
    case 180:
      upd_reg(dst, imm, st);
      upd_flag(0, st);
      return;
    case 188:
      upd_reg(dst, (unsigned int) src64, st);
      upd_flag(0, st);
      return;
    case 196:
      if (imm < 32U) {
        upd_reg(dst,
                (unsigned long long) ((int) (unsigned int) dst64 >> imm), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 204:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((int) (unsigned int) dst64
                                       >> (unsigned int) src64), st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-10, st);
        return;
      }
    case 5:
      upd_pc(pc + ofs, st);
      upd_flag(0, st);
      return;
    case 21:
      if (dst64 == (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 29:
      if (dst64 == src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 37:
      if (dst64 > (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 45:
      if (dst64 > src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 53:
      if (dst64 >= (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 61:
      if (dst64 >= src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 165:
      if (dst64 < (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 173:
      if (dst64 < src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 181:
      if (dst64 <= (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 189:
      if (dst64 <= src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 69:
      if ((dst64 & (unsigned long long) imm) != 0LLU) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 77:
      if ((dst64 & src64) != 0LLU) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 85:
      if (dst64 != (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 93:
      if (dst64 != src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 101:
      if ((long long) dst64 > (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 109:
      if ((long long) dst64 > (long long) src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 117:
      if ((long long) dst64 >= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 125:
      if ((long long) dst64 >= (long long) src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 197:
      if ((long long) dst64 < (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 205:
      if ((long long) dst64 < (long long) src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 213:
      if ((long long) dst64 <= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 221:
      if ((long long) dst64 <= (long long) src64) {
        upd_pc(pc + ofs, st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(0, st);
        return;
      }
    case 24:
      if (pc + 1LLU < len0) {
        next_ins = list_get(l0, pc + 1LLU);
        next_imm = get_immediate(next_ins);
        upd_reg(dst,
                (unsigned long long) (unsigned int) imm
                  | (unsigned long long) (unsigned int) next_imm << 32U, st);
        upd_pc_incr(st);
        upd_flag(0, st);
        return;
      } else {
        upd_flag(-5, st);
        return;
      }
    case 97:
      check_ldxw = check_mem((*st).mrs, addr_src, 4U);
      if (check_ldxw == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        v_xw = load_mem(4U, src64 + (unsigned long long) ofs, st);
        upd_reg(dst, v_xw, st);
        upd_flag(0, st);
        return;
      }
    case 105:
      check_ldxh = check_mem((*st).mrs, addr_src, 2U);
      if (check_ldxh == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        v_xh = load_mem(2U, src64 + (unsigned long long) ofs, st);
        upd_reg(dst, v_xh, st);
        upd_flag(0, st);
        return;
      }
    case 113:
      check_ldxb = check_mem((*st).mrs, addr_src, 1U);
      if (check_ldxb == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        v_xb = load_mem(1U, src64 + (unsigned long long) ofs, st);
        upd_reg(dst, v_xb, st);
        upd_flag(0, st);
        return;
      }
    case 121:
      check_ldxdw = check_mem((*st).mrs, addr_src, 8U);
      if (check_ldxdw == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        v_xdw = load_mem(8U, src64 + (unsigned long long) ofs, st);
        upd_reg(dst, v_xdw, st);
        upd_flag(0, st);
        return;
      }
    case 98:
      check_stw = check_mem((*st).mrs, addr_dst, 4U);
      if (check_stw == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_imm(4U, dst64 + (unsigned long long) ofs, imm, st);
        upd_flag(0, st);
        return;
      }
    case 106:
      check_sth = check_mem((*st).mrs, addr_dst, 2U);
      if (check_sth == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_imm(2U, dst64 + (unsigned long long) ofs, imm, st);
        upd_flag(0, st);
        return;
      }
    case 114:
      check_stb = check_mem((*st).mrs, addr_dst, 1U);
      if (check_stb == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_imm(1U, dst64 + (unsigned long long) ofs, imm, st);
        upd_flag(0, st);
        return;
      }
    case 122:
      check_stdw = check_mem((*st).mrs, addr_dst, 8U);
      if (check_stdw == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_imm(8U, dst64 + (unsigned long long) ofs, imm, st);
        upd_flag(0, st);
        return;
      }
    case 99:
      check_stxw = check_mem((*st).mrs, addr_dst, 4U);
      if (check_stxw == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_reg(4U, dst64 + (unsigned long long) ofs, src64, st);
        upd_flag(0, st);
        return;
      }
    case 107:
      check_stxh = check_mem((*st).mrs, addr_dst, 2U);
      if (check_stxh == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_reg(2U, dst64 + (unsigned long long) ofs, src64, st);
        upd_flag(0, st);
        return;
      }
    case 115:
      check_stxb = check_mem((*st).mrs, addr_dst, 1U);
      if (check_stxb == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_reg(1U, dst64 + (unsigned long long) ofs, src64, st);
        upd_flag(0, st);
        return;
      }
    case 123:
      check_stxdw = check_mem((*st).mrs, addr_dst, 8U);
      if (check_stxdw == 0LLU) {
        upd_flag(-2, st);
        return;
      } else {
        store_mem_reg(8U, dst64 + (unsigned long long) ofs, src64, st);
        upd_flag(0, st);
        return;
      }
    case 149:
      upd_flag(1, st);
      return;
    default:
      upd_flag(-1, st);
      return;
    
  }
}

/*
void bpf_interpreter_aux(unsigned long long *l1, unsigned long long len1, unsigned int fuel1, struct bpf_state *st)
{
  unsigned int fuel0;
  unsigned long long pc1;
  int f1;
  if (fuel1 == 0U) {
    upd_flag(-5, st);
    return;
  } else {
    fuel0 = fuel1 - 1U;
    pc1 = eval_pc(st);
    if (pc1 < len1) {
      step(l1, len1, st);// print_bpf_state(st);
      upd_pc_incr(st);
      f1 = eval_flag(st);
      if (f1 == 0) {
        bpf_interpreter_aux(l1, len1, fuel0, st);
        return;
      } else {
        return;
      }
    } else {
      upd_flag(-5, st);
      return;
    }
  }
} */

void bpf_interpreter_aux(unsigned long long *l1, unsigned long long len1, unsigned int fuel1, struct bpf_state *st)
{
  unsigned int fuel0;
  unsigned long long pc1;
  int f1;
  for (int i=0; i< fuel1; i++){
    pc1 = eval_pc(st);
    if (pc1 < len1) {
      step(l1, len1, st); //print_bpf_state(st);
      upd_pc_incr(st);
      f1 = eval_flag(st);
      if (f1 == 0) {
        continue;
      } else {
        return;
      }
    } else {
      upd_flag(-5, st);
      return;
    }
  }
  upd_flag(-5, st);
  return;
}

unsigned long long bpf_interpreter(unsigned long long *l2, unsigned long long len2, unsigned int fuel2, struct bpf_state *st)
{
  int f2;
  upd_reg(1U, (*(*(*st).mrs).bpf_ctx).start_addr, st);
  bpf_interpreter_aux(l2, len2, fuel2, st);
  f2 = eval_flag(st);
  if (f2 == 1) {
    return eval_reg(0U, st);
  } else {
    return 0LLU;
  }
}
