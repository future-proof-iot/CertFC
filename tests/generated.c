extern unsigned int const pc;

extern unsigned long long const init_regmap[11];

extern struct $101 const init_regs_state;

extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned long long eval_reg(unsigned int, unsigned long long [11]);

extern unsigned long long upd_reg(unsigned int, unsigned long long, unsigned long long [11])[11];

extern long long get_opcode(unsigned long long);

extern long long get_dst(unsigned long long);

extern long long get_src(unsigned long long);

extern short get_offset(unsigned long long);

extern unsigned long long get_immediate(unsigned long long);

extern unsigned long long test_int_shift(unsigned long long, unsigned long long);

extern unsigned int ins_to_opcode(unsigned long long);

extern unsigned int ins_to_dst_reg(unsigned long long);

extern unsigned int ins_to_src_reg(unsigned long long);

extern unsigned long long step(unsigned long long *, unsigned long long, unsigned long long [11])[11];

extern unsigned int const pc;

extern unsigned long long const init_regmap[11];

extern struct $101 const init_regs_state;

extern unsigned long long default_regs(void)[11];

unsigned long long list_get(unsigned long long *li, unsigned long long idx)
{
  return *(li + idx);
}

unsigned long long eval_reg(unsigned int r, unsigned long long regs[11])
{
  return *(regs + r);
}

unsigned long long upd_reg(unsigned int r$22, unsigned long long v, unsigned long long regs$24[11])[11]
{
  return *(regs$24 + r$22) = v;
}

long long get_opcode(unsigned long long i)
{
  return i & 255LL;
}

long long get_dst(unsigned long long i$26)
{
  return (i$26 & 4095LL) >> 8LL;
}

long long get_src(unsigned long long i$27)
{
  return (i$27 & 65535LL) >> 12LL;
}

short get_offset(unsigned long long i$28)
{
  return i$28 << 32LL >> 48LL;
}

unsigned long long get_immediate(unsigned long long i$29)
{
  return i$29 >> 32LL;
}

unsigned long long test_int_shift(unsigned long long i$30, unsigned long long j)
{
  return (long long) i$30 >> j;
}

unsigned int ins_to_opcode(unsigned long long i$32)
{
  long long op_z;
  op_z = get_opcode(i$32);
  return op_z;
}

unsigned int ins_to_dst_reg(unsigned long long i$34)
{
  long long dst_z;
  dst_z = get_dst(i$34);
  return dst_z;
}

unsigned int ins_to_src_reg(unsigned long long i$36)
{
  long long src_z;
  src_z = get_src(i$36);
  return src_z;
}

unsigned long long step(unsigned long long *l, unsigned long long loc, unsigned long long st[11])[11]
{
  unsigned long long ins;
  unsigned int op;
  unsigned int dst;
  unsigned int src;
  unsigned long long imm;
  unsigned long long dst64;
  unsigned long long src64;
  ins = list_get(l, loc);
  op = ins_to_opcode(ins);
  dst = ins_to_dst_reg(ins);
  src = ins_to_src_reg(ins);
  get_offset(ins);
  imm = get_immediate(ins);
  dst64 = eval_reg(dst, st);
  src64 = eval_reg(src, st);
  switch (op) {
    case 7:
      return default_regs();
    case 15:
      return default_regs();
    case 23:
      return default_regs();
    case 31:
      return default_regs();
    case 39:
      return default_regs();
    case 47:
      return default_regs();
    case 55:
      return default_regs();
    case 63:
      return default_regs();
    case 71:
      return default_regs();
    case 79:
      return default_regs();
    case 87:
      return default_regs();
    case 95:
      return default_regs();
    case 103:
      return default_regs();
    case 111:
      return default_regs();
    case 119:
      return default_regs();
    case 127:
      return default_regs();
    case 135:
      return upd_reg(dst, -dst64, st);
    case 151:
      return default_regs();
    case 159:
      return default_regs();
    case 167:
      return default_regs();
    case 175:
      return default_regs();
    case 183:
      return default_regs();
    case 191:
      return default_regs();
    case 199:
      return default_regs();
    case 207:
      return default_regs();
    case 4:
      return upd_reg(dst, (unsigned long long) ((unsigned int) dst64 + imm),
                     st);
    case 12:
      return upd_reg(dst,
                     (unsigned long long) ((unsigned int) dst64
                                            + (unsigned int) src64), 
                     st);
    case 20:
      return default_regs();
    case 28:
      return default_regs();
    case 36:
      return default_regs();
    case 44:
      return default_regs();
    case 52:
      return default_regs();
    case 60:
      return default_regs();
    case 68:
      return default_regs();
    case 76:
      return default_regs();
    case 84:
      return default_regs();
    case 92:
      return default_regs();
    case 100:
      return default_regs();
    case 108:
      return default_regs();
    case 116:
      return default_regs();
    case 124:
      return default_regs();
    case 132:
      return upd_reg(dst, (unsigned long long) -((unsigned int) dst64), st);
    case 148:
      return default_regs();
    case 156:
      return default_regs();
    case 164:
      return default_regs();
    case 172:
      return default_regs();
    case 180:
      return default_regs();
    case 188:
      return default_regs();
    case 196:
      return default_regs();
    case 204:
      return default_regs();
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


