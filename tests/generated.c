extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned char get_opcode(unsigned long long);

extern unsigned int get_dst(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern short get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern int succ_return(void);

extern int normal_return(void);

extern int ill_return(void);

extern int ill_len(void);

extern int ill_div(void);

extern int ill_shift(void);

extern int step(unsigned long long *, unsigned long long);

extern int bpf_interpreter_aux(unsigned long long *, unsigned long long, unsigned int);

extern unsigned long long bpf_interpreter(unsigned long long *, unsigned long long, unsigned int);

extern unsigned long long eval_pc(void);

extern void upd_pc(unsigned long long);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern unsigned long long eval_reg_mem(unsigned int, unsigned int);

extern void upd_reg_mem(unsigned int, unsigned int, unsigned long long);

extern unsigned long long load_mem(unsigned int, unsigned long long);

extern void store_mem(unsigned int, unsigned long long, unsigned long long);

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

int succ_return(void)
{
  return 1;
}

int normal_return(void)
{
  return 0;
}

int ill_return(void)
{
  return -1;
}

int ill_len(void)
{
  return -5;
}

int ill_div(void)
{
  return -9;
}

int ill_shift(void)
{
  return -10;
}

int step(unsigned long long *l0, unsigned long long len0)
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
  unsigned long long next_ins;
  int next_imm;
  unsigned long long v_xw;
  unsigned long long v_xh;
  unsigned long long v_xb;
  unsigned long long v_xdw;
  pc = eval_pc();
  ins = list_get(l0, pc);
  op = get_opcode(ins);
  dst = get_dst(ins);
  src = get_src(ins);
  dst64 = eval_reg(dst);
  src64 = eval_reg(src);
  ofs = get_offset(ins);
  imm = get_immediate(ins);
  switch (op) {
    case 7:
      upd_reg(dst, dst64 + (unsigned long long) imm);
      return normal_return();
    case 15:
      upd_reg(dst, dst64 + src64);
      return normal_return();
    case 23:
      upd_reg(dst, dst64 - (unsigned long long) imm);
      return normal_return();
    case 31:
      upd_reg(dst, dst64 - src64);
      return normal_return();
    case 39:
      upd_reg(dst, dst64 * (unsigned long long) imm);
      return normal_return();
    case 47:
      upd_reg(dst, dst64 * src64);
      return normal_return();
    case 55:
      if ((unsigned long long) imm != 0LLU) {
        upd_reg(dst, dst64 / (unsigned long long) imm);
        return normal_return();
      } else {
        return ill_div();
      }
    case 63:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 / src64);
        return normal_return();
      } else {
        return ill_div();
      }
    case 71:
      upd_reg(dst, dst64 | (unsigned long long) imm);
      return normal_return();
    case 79:
      upd_reg(dst, dst64 | (unsigned long long) imm);
      return normal_return();
    case 87:
      upd_reg(dst, dst64 & (unsigned long long) imm);
      return normal_return();
    case 95:
      upd_reg(dst, dst64 & (unsigned long long) imm);
      return normal_return();
    case 103:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, dst64 << imm);
        return normal_return();
      } else {
        return ill_shift();
      }
    case 111:
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 << (unsigned int) src64);
        return normal_return();
      } else {
        return ill_shift();
      }
    case 119:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, dst64 >> imm);
        return normal_return();
      } else {
        return ill_shift();
      }
    case 127:
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> (unsigned int) src64);
        return normal_return();
      } else {
        return ill_shift();
      }
    case 135:
      upd_reg(dst, -dst64);
      return normal_return();
    case 151:
      if ((unsigned long long) imm != 0LLU) {
        upd_reg(dst, dst64 % imm);
        return normal_return();
      } else {
        return ill_div();
      }
    case 159:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % (unsigned int) src64);
        return normal_return();
      } else {
        return ill_div();
      }
    case 167:
      upd_reg(dst, dst64 ^ (unsigned long long) imm);
      return normal_return();
    case 175:
      upd_reg(dst, dst64 ^ src64);
      return normal_return();
    case 183:
      upd_reg(dst, (unsigned long long) imm);
      return normal_return();
    case 191:
      upd_reg(dst, src64);
      return normal_return();
    case 199:
      if ((unsigned long long) imm < 64LLU) {
        upd_reg(dst, (long long) dst64 >> imm);
        return normal_return();
      } else {
        return ill_shift();
      }
    case 207:
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> (unsigned int) src64);
        return normal_return();
      } else {
        return ill_shift();
      }
    case 4:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 + imm));
      return normal_return();
    case 12:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     + (unsigned int) src64));
      return normal_return();
    case 20:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 - imm));
      return normal_return();
    case 28:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     - (unsigned int) src64));
      return normal_return();
    case 36:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 * imm));
      return normal_return();
    case 44:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     * (unsigned int) src64));
      return normal_return();
    case 52:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 / imm));
        return normal_return();
      } else {
        return ill_div();
      }
    case 60:
      if ((unsigned int) src64 != 0U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       / (unsigned int) src64));
        return normal_return();
      } else {
        return ill_div();
      }
    case 68:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 | imm));
      return normal_return();
    case 76:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     | (unsigned int) src64));
      return normal_return();
    case 84:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 & imm));
      return normal_return();
    case 92:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     & (unsigned int) src64));
      return normal_return();
    case 100:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 << imm));
        return normal_return();
      } else {
        return ill_shift();
      }
    case 108:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       << (unsigned int) src64));
        return normal_return();
      } else {
        return ill_shift();
      }
    case 116:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 >> imm));
        return normal_return();
      } else {
        return ill_shift();
      }
    case 124:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       >> (unsigned int) src64));
        return normal_return();
      } else {
        return ill_shift();
      }
    case 132:
      upd_reg(dst, (unsigned long long) -((unsigned int) dst64));
      return normal_return();
    case 148:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) ((unsigned int) dst64 % imm));
        return normal_return();
      } else {
        return ill_div();
      }
    case 156:
      if ((unsigned int) src64 != 0U) {
        upd_reg(dst,
                (unsigned long long) ((unsigned int) dst64
                                       % (unsigned int) src64));
        return normal_return();
      } else {
        return ill_div();
      }
    case 164:
      upd_reg(dst, (unsigned long long) ((unsigned int) dst64 ^ imm));
      return normal_return();
    case 172:
      upd_reg(dst,
              (unsigned long long) ((unsigned int) dst64
                                     ^ (unsigned int) src64));
      return normal_return();
    case 180:
      upd_reg(dst, imm);
      return normal_return();
    case 188:
      upd_reg(dst, (unsigned int) src64);
      return normal_return();
    case 196:
      if (imm < 32U) {
        upd_reg(dst,
                (unsigned long long) ((int) (unsigned int) dst64 >> imm));
        return normal_return();
      } else {
        return ill_shift();
      }
    case 204:
      if ((unsigned int) src64 < 32U) {
        upd_reg(dst,
                (unsigned long long) ((int) (unsigned int) dst64
                                       >> (unsigned int) src64));
        return normal_return();
      } else {
        return ill_shift();
      }
    case 5:
      upd_pc(pc + ofs);
      return normal_return();
    case 21:
      if (dst64 == (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 29:
      if (dst64 == src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 37:
      if (dst64 > (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 45:
      if (dst64 > src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 53:
      if (dst64 >= (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 61:
      if (dst64 >= src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 165:
      if (dst64 < (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 173:
      if (dst64 < src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 181:
      if (dst64 <= (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 189:
      if (dst64 <= src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 69:
      if ((dst64 & (unsigned long long) imm) != 0LLU) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 77:
      if ((dst64 & src64) != 0LLU) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 85:
      if (dst64 != (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 93:
      if (dst64 != src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 101:
      if ((long long) dst64 > (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 109:
      if ((long long) dst64 > (long long) src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 117:
      if ((long long) dst64 >= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 125:
      if ((long long) dst64 >= (long long) src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 197:
      if ((long long) dst64 < (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 205:
      if ((long long) dst64 < (long long) src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 213:
      if ((long long) dst64 <= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 221:
      if ((long long) dst64 <= (long long) src64) {
        upd_pc(pc + ofs);
        return normal_return();
      } else {
        return normal_return();
      }
    case 24:
      if (pc + 1LLU < len0) {
        next_ins = list_get(l0, pc + 1LLU);
        next_imm = get_immediate(next_ins);
        upd_reg(dst,
                (unsigned long long) (unsigned int) imm
                  | (unsigned long long) (unsigned int) next_imm << 32LLU);
        upd_pc(pc + 1LLU);
        return normal_return();
      } else {
        return ill_len();
      }
    case 97:
      v_xw = load_mem(32U, src64 + (unsigned long long) ofs);
      upd_reg_mem(32U, dst, v_xw);
      return normal_return();
    case 105:
      v_xh = load_mem(16U, src64 + (unsigned long long) ofs);
      upd_reg_mem(16U, dst, v_xh);
      return normal_return();
    case 113:
      v_xb = load_mem(8U, src64 + (unsigned long long) ofs);
      upd_reg_mem(8U, dst, v_xb);
      return normal_return();
    case 121:
      v_xdw = load_mem(64U, src64 + (unsigned long long) ofs);
      upd_reg_mem(64U, dst, v_xdw);
      return normal_return();
    case 98:
      store_mem(32U, dst64 + (unsigned long long) ofs,
                (unsigned long long) (unsigned int) imm);
      return normal_return();
    case 106:
      store_mem(16U, dst64 + (unsigned long long) ofs,
                (unsigned long long) (unsigned int) imm);
      return normal_return();
    case 114:
      store_mem(8U, dst64 + (unsigned long long) ofs,
                (unsigned long long) (unsigned int) imm);
      return normal_return();
    case 122:
      store_mem(64U, dst64 + (unsigned long long) ofs,
                (unsigned long long) (unsigned int) imm);
      return normal_return();
    case 99:
      store_mem(32U, dst64 + (unsigned long long) ofs, src64);
      return normal_return();
    case 107:
      store_mem(16U, dst64 + (unsigned long long) ofs, src64);
      return normal_return();
    case 115:
      store_mem(8U, dst64 + (unsigned long long) ofs, src64);
      return normal_return();
    case 123:
      store_mem(64U, dst64 + (unsigned long long) ofs, src64);
      return normal_return();
    case 149:
      return succ_return();
    default:
      return ill_return();
    
  }
}

int bpf_interpreter_aux(unsigned long long *l1, unsigned long long len1, unsigned int fuel1)
{
  unsigned int fuel0;
  unsigned long long pc1;
  int f1;
  if (fuel1 == 0U) {
    return ill_len();
  } else {
    fuel0 = fuel1 - 1U;
    pc1 = eval_pc();
    if (pc1 < len1) {
      f1 = step(l1, len1);
      upd_pc(pc1 + 1LLU);
      if (f1 == 0) {
        return bpf_interpreter_aux(l1, len1, fuel0);
      } else {
        return f1;
      }
    } else {
      return ill_len();
    }
  }
}

unsigned long long bpf_interpreter(unsigned long long *l2, unsigned long long len2, unsigned int fuel2)
{
  int f2;
  f2 = bpf_interpreter_aux(l2, len2, fuel2);
  if (f2 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


