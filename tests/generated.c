extern unsigned int const pc;

extern unsigned long long const init_regmap[11];

extern struct $101 const init_regs_state;

extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned long long return0(void);

extern unsigned long long return1(void);

extern unsigned long long return4(void);

extern unsigned long long return10(void);

extern unsigned long long test_match_reg(unsigned int);

extern unsigned long long test_reg_eval(unsigned int, unsigned long long [11]);

extern unsigned long long test_reg_upd(unsigned int, unsigned long long, unsigned long long [11])[11];

extern unsigned long long test_match_nat(unsigned int);

extern long long test_Z(void);

extern long long get_opcode(unsigned long long);

extern long long get_dst(unsigned long long);

extern long long get_src(unsigned long long);

extern short get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern unsigned long long test_int_shift(unsigned long long, unsigned long long);

extern unsigned int ins_to_opcode(unsigned long long);

extern unsigned int ins_to_dst_reg(unsigned long long);

extern unsigned int ins_to_src_reg(unsigned long long);

extern unsigned long long step(unsigned long long *, unsigned long long, unsigned long long [11])[11];

extern unsigned int const pc;

extern unsigned long long const init_regmap[11];

extern struct $101 const init_regs_state;

extern unsigned long long default_regs(void)[11];

unsigned long long list_get(unsigned long long *l, unsigned long long idx)
{
  return *(l + idx);
}

unsigned long long return0(void)
{
  return 0LLU;
}

unsigned long long return1(void)
{
  return 1LLU;
}

unsigned long long return4(void)
{
  return 64LLU;
}

unsigned long long return10(void)
{
  return 0LLU;
}

unsigned long long test_match_reg(unsigned int r)
{
  switch (r) {
    case 0:
      return return0();
    case 1:
      return return1();
    case 2:
      return return10();
    case 3:
      return return10();
    case 4:
      return return4();
    
  }
}

unsigned long long test_reg_eval(unsigned int r$28, unsigned long long regs[11])
{
  return *(regs + r$28);
}

unsigned long long test_reg_upd(unsigned int r$30, unsigned long long v, unsigned long long regs$32[11])[11]
{
  return *(regs$32 + r$30) = v;
}

unsigned long long test_match_nat(unsigned int n)
{
  unsigned int n0;
  unsigned int n1;
  if (n == 0U) {
    return return0();
  } else {
    n0 = n - 1U;
    if (n0 == 0U) {
      return return1();
    } else {
      n1 = n0 - 1U;
      if (n1 == 0U) {
        return return10();
      } else {
        return return0();
      }
    }
  }
}

long long test_Z(void)
{
  return 7LL;
}

long long get_opcode(unsigned long long i)
{
  return i & 255LL;
}

long long get_dst(unsigned long long i$38)
{
  return (i$38 & 4095LL) >> 8LL;
}

long long get_src(unsigned long long i$39)
{
  return (i$39 & 65535LL) >> 12LL;
}

short get_offset(unsigned long long i$40)
{
  return i$40 << 32LL >> 48LL;
}

int get_immediate(unsigned long long i$41)
{
  return i$41 >> 32LL;
}

unsigned long long test_int_shift(unsigned long long i$42, unsigned long long j)
{
  return (long long) i$42 >> j;
}

unsigned int ins_to_opcode(unsigned long long ins)
{
  long long op_z;
  op_z = get_opcode(ins);
  return op_z;
}

unsigned int ins_to_dst_reg(unsigned long long ins$46)
{
  long long dst_z;
  dst_z = get_dst(ins$46);
  return dst_z;
}

unsigned int ins_to_src_reg(unsigned long long ins$48)
{
  long long src_z;
  src_z = get_src(ins$48);
  return src_z;
}

unsigned long long step(unsigned long long *l$50, unsigned long long loc, unsigned long long st[11])[11]
{
  unsigned long long ins$53;
  unsigned int op;
  unsigned int dst;
  unsigned long long dst64;
  ins$53 = list_get(l$50, loc);
  op = ins_to_opcode(ins$53);
  dst = ins_to_dst_reg(ins$53);
  ins_to_src_reg(ins$53);
  get_offset(ins$53);
  get_immediate(ins$53);
  switch (op) {
    case 132:
      dst64 = test_reg_eval(dst, st);
      return test_reg_upd(dst, (unsigned long long) -((unsigned int) dst64),
                          st);
    case 135:
      return default_regs();
    case 12:
      return default_regs();
    case 4:
      return default_regs();
    case 15:
      return default_regs();
    case 7:
      return default_regs();
    case 149:
      return default_regs();
    default:
      return default_regs();
    
  }
}


