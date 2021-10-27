extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned char get_opcode(unsigned long long);

extern unsigned int get_dst(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern short get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern unsigned long long get_addl(unsigned long long, unsigned long long);

extern unsigned long long getMemRegion_block_ptr(struct $1004);

extern unsigned long long getMemRegion_start_addr(struct $1004);

extern unsigned long long getMemRegion_block_size(struct $1004);

extern struct $1004 getMemRegions_bpf_ctx(struct $1007);

extern struct $1004 getMemRegions_bpf_stk(struct $1007);

extern struct $1004 getMemRegions_content(struct $1007);

extern unsigned long long get_subl(unsigned long long, unsigned long long);

extern unsigned long long check_mem_aux(struct $1004, unsigned long long, unsigned int);

extern unsigned long long check_mem(struct $1007, unsigned long long, unsigned int);

extern void step(unsigned long long *, unsigned long long, struct $1007);

extern void bpf_interpreter_aux(unsigned long long *, unsigned long long, struct $1007, unsigned int);

extern unsigned long long bpf_interpreter(unsigned long long *, unsigned long long, struct $1007, unsigned int);

extern unsigned long long test_reg_eval(unsigned int, unsigned long long [11]);

extern unsigned long long test_reg_upd(unsigned int, unsigned long long, unsigned long long [11])[11];

extern unsigned long long eval_pc(void);

extern void upd_pc(unsigned long long);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern int eval_flag(void);

extern void upd_flag(int);

extern unsigned long long load_mem(unsigned int, unsigned long long);

extern void store_mem_imm(unsigned int, unsigned long long, int);

extern void store_mem_reg(unsigned int, unsigned long long, unsigned long long);

unsigned long long list_get(unsigned long long *l, unsigned long long idx0)
{
  return *(l + idx0);
}

unsigned char get_opcode(unsigned long long ins0)
{
  return (unsigned char) (ins0 & 255LLU);
}

unsigned int get_dst(unsigned long long ins1)
{
  return (unsigned int) ((ins1 & 4095LLU) >> 8LLU);
}

unsigned int get_src(unsigned long long ins2)
{
  return (unsigned int) ((ins2 & 65535LLU) >> 12LLU);
}

short get_offset(unsigned long long i0)
{
  return (short) (i0 << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long i1)
{
  return (int) (i1 >> 32LLU);
}

unsigned long long get_addl(unsigned long long x, unsigned long long y)
{
  return x + y;
}

unsigned long long getMemRegion_block_ptr(struct $1004 mr0)
{
  return 1LLU;
}

unsigned long long getMemRegion_start_addr(struct $1004 mr1)
{
  return mr1.$1005;
}

unsigned long long getMemRegion_block_size(struct $1004 mr2)
{
  return mr2.$1006;
}

struct $1004 getMemRegions_bpf_ctx(struct $1007 mrs0)
{
  return mrs0.$1008;
}

struct $1004 getMemRegions_bpf_stk(struct $1007 mrs1)
{
  return mrs1.$1009;
}

struct $1004 getMemRegions_content(struct $1007 mrs2)
{
  return mrs2.$1010;
}

unsigned long long get_subl(unsigned long long x1, unsigned long long y1)
{
  return x1 - y1;
}

unsigned long long check_mem_aux(struct $1004 mr, unsigned long long addr0, unsigned int chunk0)
{
  unsigned long long ptr;
  unsigned long long start;
  unsigned long long size;
  unsigned long long lo_ofs;
  unsigned long long hi_ofs;
  ptr = getMemRegion_block_ptr(mr);
  start = getMemRegion_start_addr(mr);
  size = getMemRegion_block_size(mr);
  lo_ofs = get_subl(addr0, start);
  hi_ofs = get_addl(lo_ofs, chunk0);
  if (0LLU <= lo_ofs && hi_ofs < size) {
    if (lo_ofs <= 18446744073709551615LLU - chunk0 && 0LLU == lo_ofs % chunk0) {
      return ptr + lo_ofs;
    } else {
      return 0LLU;
    }
  } else {
    return 0LLU;
  }
}

unsigned long long check_mem(struct $1007 mrs6, unsigned long long addr1, unsigned int chunk1)
{
  unsigned long long check_mem_ctx;
  unsigned long long check_mem_stk;
  unsigned long long check_mem_content;
  check_mem_ctx = check_mem_aux(mrs6.$1008, addr1, chunk1);
  if (check_mem_ctx == 0LLU) {
    check_mem_stk = check_mem_aux(mrs6.$1009, addr1, chunk1);
    if (check_mem_stk == 0LLU) {
      check_mem_content = check_mem_aux(mrs6.$1010, addr1, chunk1);
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

void step(unsigned long long *l0, unsigned long long len0, struct $1007 mrs)
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
  pc = eval_pc();
  ins = list_get(l0, pc);
  op = get_opcode(ins);
  dst = get_dst(ins);
  src = get_src(ins);
  dst64 = eval_reg(dst);
  src64 = eval_reg(src);
  ofs = get_offset(ins);
  imm = get_immediate(ins);
  addr_dst = get_addl(dst64, ofs);
  addr_src = get_addl(src64, ofs);
  switch (op) {
    case 7:
      upd_reg(dst, dst64 + (unsigned long long) imm);
      upd_flag(0);
      return;
    case 15:
      upd_reg(dst, dst64 + src64);
      upd_flag(0);
      return;
    case 23:
      upd_reg(dst, dst64 - (unsigned long long) imm);
      upd_flag(0);
      return;
    case 31:
      upd_reg(dst, dst64 - src64);
      upd_flag(0);
      return;
    case 39:
      upd_reg(dst, dst64 * (unsigned long long) imm);
      upd_flag(0);
      return;
    case 47:
      upd_reg(dst, dst64 * src64);
      upd_flag(0);
      return;
    case 55:
      if ((unsigned long long) imm != 0LLU) {
        upd_reg(dst, dst64 / (unsigned long long) imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 63:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 / src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 71:
      upd_reg(dst, dst64 | (unsigned long long) imm);
      upd_flag(0);
      return;
    case 79:
      upd_reg(dst, dst64 | src64);
      upd_flag(0);
      return;
    case 87:
      upd_reg(dst, dst64 & (unsigned long long) imm);
      upd_flag(0);
      return;
    case 95:
      upd_reg(dst, dst64 & src64);
      upd_flag(0);
      return;
    case 103:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, dst64 << imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 111:
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 << (unsigned int) src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 119:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, dst64 >> imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 127:
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> (unsigned int) src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 135:
      upd_reg(dst, -dst64);
      upd_flag(0);
      return;
    case 151:
      if ((unsigned long long) imm != 0LLU) {
        upd_reg(dst, dst64 % imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 159:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % (unsigned int) src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 167:
      upd_reg(dst, dst64 ^ (unsigned long long) imm);
      upd_flag(0);
      return;
    case 175:
      upd_reg(dst, dst64 ^ src64);
      upd_flag(0);
      return;
    case 183:
      upd_reg(dst, (unsigned long long) imm);
      upd_flag(0);
      return;
    case 191:
      upd_reg(dst, src64);
      upd_flag(0);
      return;
    case 199:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, (long long) dst64 >> imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 207:
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> (unsigned int) src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 4:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 + imm));
      upd_flag(0);
      return;
    case 12:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     + (unsigned int) src64));
      upd_flag(0);
      return;
    case 20:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 - imm));
      upd_flag(0);
      return;
    case 28:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     - (unsigned int) src64));
      upd_flag(0);
      return;
    case 36:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 * imm));
      upd_flag(0);
      return;
    case 44:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     * (unsigned int) src64));
      upd_flag(0);
      return;
    case 52:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 / imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 60:
      if ((unsigned int) src64 != 0U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       / (unsigned int) src64));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 68:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 | imm));
      upd_flag(0);
      return;
    case 76:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     | (unsigned int) src64));
      upd_flag(0);
      return;
    case 84:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 & imm));
      upd_flag(0);
      return;
    case 92:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     & (unsigned int) src64));
      upd_flag(0);
      return;
    case 100:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 << imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 108:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       << (unsigned int) src64));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 116:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 >> imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 124:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       >> (unsigned int) src64));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 132:
      upd_reg(dst, (unsigned long long) -((unsigned int) dst64));
      upd_flag(0);
      return;
    case 148:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 % imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 156:
      if ((unsigned int) src64 != 0U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       % (unsigned int) src64));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 164:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 ^ imm));
      upd_flag(0);
      return;
    case 172:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     ^ (unsigned int) src64));
      upd_flag(0);
      return;
    case 180:
      upd_reg(dst, imm);
      upd_flag(0);
      return;
    case 188:
      upd_reg(dst, (unsigned int) src64);
      upd_flag(0);
      return;
    case 196:
      if (imm < 32U) {
        upd_reg(dst,
                (unsigned long long) ((int) (unsigned int) dst64 >> imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 204:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((int) (unsigned int) dst64
                                       >> (unsigned int) src64));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 5:
      upd_pc(pc + ofs);
      upd_flag(0);
      return;
    case 21:
      if (dst64 == (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 29:
      if (dst64 == src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 37:
      if (dst64 > (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 45:
      if (dst64 > src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 53:
      if (dst64 >= (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 61:
      if (dst64 >= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 165:
      if (dst64 < (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 173:
      if (dst64 < src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 181:
      if (dst64 <= (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 189:
      if (dst64 <= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 69:
      if ((dst64 & (unsigned long long) imm) != 0LLU) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 77:
      if ((dst64 & src64) != 0LLU) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 85:
      if (dst64 != (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 93:
      if (dst64 != src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 101:
      if ((long long) dst64 > (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 109:
      if ((long long) dst64 > (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 117:
      if ((long long) dst64 >= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 125:
      if ((long long) dst64 >= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 197:
      if ((long long) dst64 < (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 205:
      if ((long long) dst64 < (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 213:
      if ((long long) dst64 <= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 221:
      if ((long long) dst64 <= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 24:
      if (pc + 1LLU < len0) {
        next_ins = list_get(l0, pc + 1LLU);
        next_imm = get_immediate(next_ins);
        upd_reg(dst,
                (unsigned long long) (unsigned int) imm
                  | (unsigned long long) (unsigned int) next_imm << 32LLU);
        upd_pc(pc + 1LLU);
        upd_flag(0);
        return;
      } else {
        upd_flag(-5);
        return;
      }
    case 97:
      check_ldxw = check_mem(mrs, addr_src, 4U);
      if (check_ldxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xw = load_mem(4U, src64 + (unsigned long long) ofs);
        upd_reg(dst, v_xw);
        upd_flag(0);
        return;
      }
    case 105:
      check_ldxh = check_mem(mrs, addr_src, 2U);
      if (check_ldxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xh = load_mem(2U, src64 + (unsigned long long) ofs);
        upd_reg(dst, v_xh);
        upd_flag(0);
        return;
      }
    case 113:
      check_ldxb = check_mem(mrs, addr_src, 1U);
      if (check_ldxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xb = load_mem(1U, src64 + (unsigned long long) ofs);
        upd_reg(dst, v_xb);
        upd_flag(0);
        return;
      }
    case 121:
      check_ldxdw = check_mem(mrs, addr_src, 8U);
      if (check_ldxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xdw = load_mem(8U, src64 + (unsigned long long) ofs);
        upd_reg(dst, v_xdw);
        upd_flag(0);
        return;
      }
    case 98:
      check_stw = check_mem(mrs, addr_dst, 4U);
      if (check_stw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, dst64 + (unsigned long long) ofs, imm);
        upd_flag(0);
        return;
      }
    case 106:
      check_sth = check_mem(mrs, addr_dst, 2U);
      if (check_sth == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, dst64 + (unsigned long long) ofs, imm);
        upd_flag(0);
        return;
      }
    case 114:
      check_stb = check_mem(mrs, addr_dst, 1U);
      if (check_stb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, dst64 + (unsigned long long) ofs, imm);
        upd_flag(0);
        return;
      }
    case 122:
      check_stdw = check_mem(mrs, addr_dst, 8U);
      if (check_stdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, dst64 + (unsigned long long) ofs, imm);
        upd_flag(0);
        return;
      }
    case 99:
      check_stxw = check_mem(mrs, addr_dst, 4U);
      if (check_stxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, dst64 + (unsigned long long) ofs, src64);
        upd_flag(0);
        return;
      }
    case 107:
      check_stxh = check_mem(mrs, addr_dst, 2U);
      if (check_stxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, dst64 + (unsigned long long) ofs, src64);
        upd_flag(0);
        return;
      }
    case 115:
      check_stxb = check_mem(mrs, addr_dst, 1U);
      if (check_stxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, dst64 + (unsigned long long) ofs, src64);
        upd_flag(0);
        return;
      }
    case 123:
      check_stxdw = check_mem(mrs, addr_dst, 8U);
      if (check_stxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, dst64 + (unsigned long long) ofs, src64);
        upd_flag(0);
        return;
      }
    case 149:
      upd_flag(1);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned long long *l1, unsigned long long len1, struct $1007 mrs3, unsigned int fuel1)
{
  unsigned int fuel0;
  unsigned long long pc1;
  int f1;
  if (fuel1 == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel1 - 1U;
    pc1 = eval_pc();
    if (pc1 < len1) {
      step(l1, len1, mrs3);
      upd_pc(pc1 + 1LLU);
      f1 = eval_flag();
      if (f1 == 0) {
        bpf_interpreter_aux(l1, len1, mrs3, fuel0);
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

unsigned long long bpf_interpreter(unsigned long long *l2, unsigned long long len2, struct $1007 mrs4, unsigned int fuel2)
{
  int f2;
  bpf_interpreter_aux(l2, len2, mrs4, fuel2);
  f2 = eval_flag();
  if (f2 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}

unsigned long long test_reg_eval(unsigned int r0, unsigned long long regs0[11])
{
  return *(regs0 + r0);
}

unsigned long long test_reg_upd(unsigned int r1, unsigned long long v, unsigned long long regs1[11])[11]
{
  return *(regs1 + r1) = v;
}


