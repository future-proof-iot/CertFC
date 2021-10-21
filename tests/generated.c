extern unsigned long long const pc;

extern unsigned long long const regs[11];

extern struct $101 const init_regs_state;

extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned long long eval_reg(unsigned int);

extern unsigned long long upd_reg(unsigned int, unsigned long long)[11];

extern long long get_opcode(unsigned long long);

extern long long get_dst(unsigned long long);

extern long long get_src(unsigned long long);

extern short get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern unsigned int ins_to_opcode(unsigned long long);

extern unsigned int ins_to_dst_reg(unsigned long long);

extern unsigned int ins_to_src_reg(unsigned long long);

extern unsigned long long step(unsigned long long *)[11];

extern unsigned long long const pc;

extern unsigned long long const regs[11];

extern struct $101 const init_regs_state;

extern unsigned long long default_regs(void)[11];

unsigned long long list_get(unsigned long long *li, unsigned long long idx)
{
  return *(li + idx);
}

unsigned long long eval_reg(unsigned int r)
{
  return *(regs + r);
}

unsigned long long upd_reg(unsigned int r$20, unsigned long long v)[11]
{
  return *(regs + r$20) = v;
}

long long get_opcode(unsigned long long i)
{
  return i & 255LL;
}

long long get_dst(unsigned long long i$23)
{
  return (i$23 & 4095LL) >> 8LL;
}

long long get_src(unsigned long long i$24)
{
  return (i$24 & 65535LL) >> 12LL;
}

short get_offset(unsigned long long i$25)
{
  return i$25 << 32LL >> 48LL;
}

int get_immediate(unsigned long long i$26)
{
  return (int) (i$26 >> 32LL);
}

unsigned int ins_to_opcode(unsigned long long i$27)
{
  long long op_z;
  op_z = get_opcode(i$27);
  return op_z;
}

unsigned int ins_to_dst_reg(unsigned long long i$29)
{
  long long dst_z;
  dst_z = get_dst(i$29);
  return dst_z;
}

unsigned int ins_to_src_reg(unsigned long long i$31)
{
  long long src_z;
  src_z = get_src(i$31);
  return src_z;
}

unsigned long long step(unsigned long long *l)[11]
{
  unsigned long long ins;
  unsigned int op;
  unsigned int dst;
  unsigned int src;
  int imm;
  unsigned long long dst64;
  unsigned long long src64;
  ins = list_get(l, pc);
  op = ins_to_opcode(ins);
  dst = ins_to_dst_reg(ins);
  src = ins_to_src_reg(ins);
  get_offset(ins);
  imm = get_immediate(ins);
  dst64 = eval_reg(dst);
  src64 = eval_reg(src);
  switch (op) {
    case 7:
      return upd_reg(dst, dst64 + (unsigned long long) imm);
    case 15:
      return upd_reg(dst, dst64 + src64);
    case 23:
      return upd_reg(dst, dst64 - (unsigned long long) imm);
    case 31:
      return upd_reg(dst, dst64 - src64);
    case 39:
      return upd_reg(dst, dst64 * (unsigned long long) imm);
    case 47:
      return upd_reg(dst, dst64 * src64);
    case 55:
      return upd_reg(dst, dst64 / (unsigned long long) imm);
    case 63:
      return upd_reg(dst, dst64 / src64);
    case 71:
      return upd_reg(dst, dst64 | (unsigned long long) imm);
    case 79:
      return upd_reg(dst, dst64 | src64);
    case 87:
      return upd_reg(dst, dst64 & (unsigned long long) imm);
    case 95:
      return upd_reg(dst, dst64 & src64);
    case 103:
      return upd_reg(dst, dst64 << (unsigned long long) imm);
    case 111:
      return upd_reg(dst, dst64 << src64);
    case 119:
      return upd_reg(dst, dst64 >> (unsigned long long) imm);
    case 127:
      return upd_reg(dst, dst64 >> src64);
    case 135:
      return upd_reg(dst, -dst64);
    case 151:
      return upd_reg(dst, dst64 % (unsigned long long) imm);
    case 159:
      return upd_reg(dst, dst64 % src64);
    case 167:
      return upd_reg(dst, dst64 ^ (unsigned long long) imm);
    case 175:
      return upd_reg(dst, dst64 ^ src64);
    case 183:
      return upd_reg(dst, (unsigned long long) imm);
    case 191:
      return upd_reg(dst, src64);
    case 199:
      return upd_reg(dst, (long long) dst64 >> (unsigned long long) imm);
    case 207:
      return upd_reg(dst, (long long) dst64 >> src64);
    case 4:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 + imm));
    case 12:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            + (unsigned int) src64));
    case 20:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 - imm));
    case 28:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            - (unsigned int) src64));
    case 36:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 * imm));
    case 44:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            * (unsigned int) src64));
    case 52:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 / imm));
    case 60:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            / (unsigned int) src64));
    case 68:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 | imm));
    case 76:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            | (unsigned int) src64));
    case 84:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 & imm));
    case 92:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            & (unsigned int) src64));
    case 100:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 << imm));
    case 108:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            << (unsigned int) src64));
    case 116:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 >> imm));
    case 124:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            >> (unsigned int) src64));
    case 132:
      return upd_reg(dst, (unsigned long long) -((unsigned int) dst64));
    case 148:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 % imm));
    case 156:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            % (unsigned int) src64));
    case 164:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 ^ imm));
    case 172:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            ^ (unsigned int) src64));
    case 180:
      return upd_reg(dst, imm);
    case 188:
      return upd_reg(dst, (unsigned int) src64);
    case 196:
      return upd_reg(dst,
                     (unsigned long long) ((int) (unsigned int) dst64 >> imm));
    case 204:
      return upd_reg(dst,
                     (unsigned long long) ((int) (unsigned int) dst64
                                            >> (unsigned int) src64));
    case 5:
      return default_regs();
    case 21:
      return default_regs();
    case 29:
      return default_regs();
    case 37:
      return default_regs();
    case 45:
      return default_regs();
    case 53:
      return default_regs();
    case 61:
      return default_regs();
    case 165:
      return default_regs();
    case 173:
      return default_regs();
    case 181:
      return default_regs();
    case 189:
      return default_regs();
    case 69:
      return default_regs();
    case 77:
      return default_regs();
    case 85:
      return default_regs();
    case 93:
      return default_regs();
    case 101:
      return default_regs();
    case 109:
      return default_regs();
    case 117:
      return default_regs();
    case 125:
      return default_regs();
    case 197:
      return default_regs();
    case 205:
      return default_regs();
    case 213:
      return default_regs();
    case 221:
      return default_regs();
    case 24:
      return default_regs();
    case 97:
      return default_regs();
    case 105:
      return default_regs();
    case 113:
      return default_regs();
    case 121:
      return default_regs();
    case 98:
      return default_regs();
    case 106:
      return default_regs();
    case 114:
      return default_regs();
    case 122:
      return default_regs();
    case 99:
      return default_regs();
    case 107:
      return default_regs();
    case 115:
      return default_regs();
    case 123:
      return default_regs();
    case 149:
      return default_regs();
    default:
      return default_regs();
    
  }
}


