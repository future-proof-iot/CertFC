struct memory_region;
struct bpf_state;
struct memory_region {
  unsigned long long start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned long long block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned int mem_num;
  unsigned long long regsmap[11];
  struct memory_region *mrs$757165;
};

extern struct bpf_state add_mem_region;

extern struct bpf_state add_mem_region_ctx;

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

extern unsigned long long get_addl(unsigned long long, unsigned long long);

extern unsigned long long get_subl(unsigned long long, unsigned long long);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned long long check_mem_aux2(struct memory_region *, unsigned long long, unsigned int);

extern unsigned long long check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned long long);

extern unsigned long long check_mem(unsigned int, unsigned int, unsigned long long);

extern _Bool comp_and_0x08_byte(unsigned char);

extern void step_opcode_alu64(unsigned int, unsigned long long, unsigned long long, unsigned char);

extern void step_opcode_alu32(unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_branch(int, int, unsigned long long, unsigned long long, unsigned char);

extern void step_opcode_mem_ld_imm(int, int, unsigned int, unsigned long long, int, unsigned char, unsigned long long *);

extern void step_opcode_mem_ld_reg(int, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long);

extern void step_opcode_mem_st_imm(int, unsigned int, unsigned long long, int, unsigned char, unsigned long long, unsigned long long);

extern void step_opcode_mem_st_reg(int, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long);

extern void step(int, unsigned long long *);

extern void bpf_interpreter_aux(int, unsigned int, unsigned long long *);

extern unsigned long long bpf_interpreter(int, unsigned int, unsigned long long *);

extern int eval_pc(void);

extern void upd_pc(int);

extern void upd_pc_incr(void);

extern int eval_flag(void);

extern void upd_flag(int);

extern unsigned int eval_mem_num(void);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern struct memory_region *eval_mem_regions(void);

extern struct bpf_state add_mem_region;

extern struct bpf_state add_mem_region_ctx;

extern unsigned long long load_mem(unsigned int, unsigned long long);

extern void store_mem_imm(unsigned int, unsigned long long, int);

extern void store_mem_reg(unsigned int, unsigned long long, unsigned long long);

unsigned long long list_get(unsigned long long *l, int idx)
{
  return *(l + idx);
}

struct memory_region *get_mem_region(unsigned int n)
{
  struct memory_region *mrs;
  mrs = eval_mem_regions();
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

unsigned int get_src(unsigned long long ins$110)
{
  return (unsigned int) ((ins$110 & 65535LLU) >> 12LLU);
}

int get_offset(unsigned long long ins$112)
{
  return (int) (short) (ins$112 << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins$114)
{
  return (int) (ins$114 >> 32LLU);
}

unsigned long long eval_immediate(int ins$116)
{
  return (unsigned long long) ins$116;
}

unsigned char get_opcode_ins(unsigned long long ins$118)
{
  return (unsigned char) (ins$118 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$122)
{
  return (unsigned char) (op$122 & 240);
}

unsigned char get_opcode_branch(unsigned char op$124)
{
  return (unsigned char) (op$124 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$126)
{
  return (unsigned char) (op$126 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$128)
{
  return (unsigned char) (op$128 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$130)
{
  return (unsigned char) (op$130 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$132)
{
  return (unsigned char) (op$132 & 255);
}

unsigned char get_opcode(unsigned char op$134)
{
  return (unsigned char) (op$134 & 7);
}

unsigned long long get_addl(unsigned long long x, unsigned long long y)
{
  return x + y;
}

unsigned long long get_subl(unsigned long long x$140, unsigned long long y$142)
{
  return x$140 - y$142;
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

unsigned long long check_mem_aux2(struct memory_region *mr, unsigned long long addr, unsigned int chunk$150)
{
  _Bool well_chunk;
  unsigned long long lo_ofs;
  unsigned long long hi_ofs;
  well_chunk = is_well_chunk_bool(chunk$150);
  if (well_chunk) {
    lo_ofs = get_subl(addr, (*mr).start_addr);
    hi_ofs = get_addl(lo_ofs, (unsigned long long) chunk$150);
    if (0LLU <= lo_ofs && hi_ofs < (*mr).block_size) {
      if (lo_ofs <= 18446744073709551615LLU - (unsigned long long) chunk$150
            && 0LLU == lo_ofs % (unsigned long long) chunk$150) {
        return 1LLU + lo_ofs;
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

unsigned long long check_mem_aux(unsigned int num, unsigned int perm, unsigned int chunk$162, unsigned long long addr$164)
{
  unsigned int n$166;
  struct memory_region *cur_mr;
  unsigned long long check_mem$170;
  if (num == 0U) {
    return 0LLU;
  } else {
    n$166 = num - 1U;
    cur_mr = get_mem_region(n$166);
    if ((*cur_mr).block_perm >= perm) {
      check_mem$170 = check_mem_aux2(cur_mr, addr$164, chunk$162);
      if (check_mem$170 == 0LLU) {
        return check_mem_aux(n$166, perm, chunk$162, addr$164);
      } else {
        return check_mem$170;
      }
    } else {
      return check_mem_aux(n$166, perm, chunk$162, addr$164);
    }
  }
}

unsigned long long check_mem(unsigned int perm$172, unsigned int chunk$174, unsigned long long addr$176)
{
  _Bool well_chunk$178;
  unsigned int mem_reg_num;
  unsigned long long check_mem$182;
  well_chunk$178 = is_well_chunk_bool(chunk$174);
  if (well_chunk$178) {
    mem_reg_num = eval_mem_num();
    check_mem$182 = check_mem_aux(mem_reg_num, perm$172, chunk$174, addr$176);
    if (check_mem$182 == 0LLU) {
      return 0LLU;
    } else {
      return check_mem$182;
    }
  } else {
    return 0LLU;
  }
}

_Bool comp_and_0x08_byte(unsigned char x$184)
{
  return 0 == (x$184 & 8);
}

void step_opcode_alu64(unsigned int dst, unsigned long long dst64, unsigned long long src64, unsigned char op$192)
{
  unsigned char opcode_alu64;
  unsigned int src32;
  unsigned int src32$198;
  unsigned int src32$200;
  unsigned int src32$202;
  opcode_alu64 = get_opcode_alu64(op$192);
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
      src32$198 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> src32$198);
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
      src32$200 = reg64_to_reg32(src64);
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % src32$200);
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
      src32$202 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> src32$202);
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

void step_opcode_alu32(unsigned int dst$204, unsigned int dst32, unsigned int src32$208, unsigned char op$210)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$210);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$204, (unsigned long long) (dst32 + src32$208));
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst$204, (unsigned long long) (dst32 - src32$208));
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst$204, (unsigned long long) (dst32 * src32$208));
      upd_flag(0);
      return;
    case 48:
      if (src32$208 != 0U) {
        upd_reg(dst$204, (unsigned long long) (dst32 / src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$204, (unsigned long long) (dst32 | src32$208));
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst$204, (unsigned long long) (dst32 & src32$208));
      upd_flag(0);
      return;
    case 96:
      if (src32$208 < 32U) {
        upd_reg(dst$204, (unsigned long long) (dst32 << src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$208 < 32U) {
        upd_reg(dst$204, (unsigned long long) (dst32 >> src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst$204, (unsigned long long) -dst32);
      upd_flag(0);
      return;
    case 144:
      if (src32$208 != 0U) {
        upd_reg(dst$204, (unsigned long long) (dst32 % src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$204, (unsigned long long) (dst32 ^ src32$208));
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst$204, src32$208);
      upd_flag(0);
      return;
    case 192:
      if (src32$208 < 32U) {
        upd_reg(dst$204, (unsigned long long) ((int) dst32 >> src32$208));
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

void step_opcode_branch(int pc, int ofs, unsigned long long dst64$218, unsigned long long src64$220, unsigned char op$222)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op$222);
  switch (opcode_jmp) {
    case 0:
      upd_pc(pc + ofs);
      upd_flag(0);
      return;
    case 16:
      if (dst64$218 == src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 32:
      if (dst64$218 > src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 48:
      if (dst64$218 >= src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 160:
      if (dst64$218 < src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 176:
      if (dst64$218 <= src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 64:
      if ((dst64$218 & src64$220) != 0LLU) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 80:
      if (dst64$218 != src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 96:
      if ((long long) dst64$218 > (long long) src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 112:
      if ((long long) dst64$218 >= (long long) src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 192:
      if ((long long) dst64$218 < (long long) src64$220) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 208:
      if ((long long) dst64$218 <= (long long) src64$220) {
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

void step_opcode_mem_ld_imm(int pc$226, int len, unsigned int dst$230, unsigned long long dst64$232, int imm, unsigned char op$236, unsigned long long *l$238)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  opcode_ld = get_opcode_mem_ld_imm(op$236);
  switch (opcode_ld) {
    case 24:
      if (pc$226 + 1 < len) {
        next_ins = list_get(l$238, pc$226 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$230,
                (unsigned long long) (unsigned int) imm
                  | (unsigned long long) (unsigned int) next_imm << 32U);
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

void step_opcode_mem_ld_reg(int pc$246, unsigned int dst$248, unsigned long long dst64$250, unsigned long long src64$252, unsigned char op$254, unsigned long long ofs64, unsigned long long addr$258)
{
  unsigned char opcode_ld$260;
  unsigned long long check_ld;
  unsigned long long v;
  unsigned long long check_ld$266;
  unsigned long long v$268;
  unsigned long long check_ld$270;
  unsigned long long v$272;
  unsigned long long check_ld$274;
  unsigned long long v$276;
  opcode_ld$260 = get_opcode_mem_ld_reg(op$254);
  switch (opcode_ld$260) {
    case 97:
      check_ld = check_mem(1U, 4U, addr$258);
      if (check_ld == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, src64$252 + ofs64);
        upd_reg(dst$248, v);
        upd_flag(0);
        return;
      }
    case 105:
      check_ld$266 = check_mem(1U, 2U, addr$258);
      if (check_ld$266 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v$268 = load_mem(2U, src64$252 + ofs64);
        upd_reg(dst$248, v$268);
        upd_flag(0);
        return;
      }
    case 113:
      check_ld$270 = check_mem(1U, 1U, addr$258);
      if (check_ld$270 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v$272 = load_mem(1U, src64$252 + ofs64);
        upd_reg(dst$248, v$272);
        upd_flag(0);
        return;
      }
    case 121:
      check_ld$274 = check_mem(1U, 8U, addr$258);
      if (check_ld$274 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v$276 = load_mem(8U, src64$252 + ofs64);
        upd_reg(dst$248, v$276);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int pc$278, unsigned int dst$280, unsigned long long dst64$282, int imm$284, unsigned char op$286, unsigned long long ofs64$288, unsigned long long addr$290)
{
  unsigned char opcode_st;
  unsigned long long check_st;
  unsigned long long check_st$296;
  unsigned long long check_st$298;
  unsigned long long check_st$300;
  opcode_st = get_opcode_mem_st_imm(op$286);
  switch (opcode_st) {
    case 98:
      check_st = check_mem(2U, 4U, addr$290);
      if (check_st == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, dst64$282 + ofs64$288, imm$284);
        upd_flag(0);
        return;
      }
    case 106:
      check_st$296 = check_mem(2U, 2U, addr$290);
      if (check_st$296 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, dst64$282 + ofs64$288, imm$284);
        upd_flag(0);
        return;
      }
    case 114:
      check_st$298 = check_mem(2U, 1U, addr$290);
      if (check_st$298 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, dst64$282 + ofs64$288, imm$284);
        upd_flag(0);
        return;
      }
    case 122:
      check_st$300 = check_mem(2U, 8U, addr$290);
      if (check_st$300 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, dst64$282 + ofs64$288, imm$284);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(int pc$302, unsigned int dst$304, unsigned long long dst64$306, unsigned long long src64$308, unsigned char op$310, unsigned long long ofs64$312, unsigned long long addr$314)
{
  unsigned char opcode_st$316;
  unsigned long long check_st$318;
  unsigned long long check_st$320;
  unsigned long long check_st$322;
  unsigned long long check_st$324;
  opcode_st$316 = get_opcode_mem_st_reg(op$310);
  switch (opcode_st$316) {
    case 99:
      check_st$318 = check_mem(2U, 4U, addr$314);
      if (check_st$318 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, dst64$306 + ofs64$312, src64$308);
        upd_flag(0);
        return;
      }
    case 107:
      check_st$320 = check_mem(2U, 2U, addr$314);
      if (check_st$320 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, dst64$306 + ofs64$312, src64$308);
        upd_flag(0);
        return;
      }
    case 115:
      check_st$322 = check_mem(2U, 1U, addr$314);
      if (check_st$322 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, dst64$306 + ofs64$312, src64$308);
        upd_flag(0);
        return;
      }
    case 123:
      check_st$324 = check_mem(2U, 8U, addr$314);
      if (check_st$324 == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, dst64$306 + ofs64$312, src64$308);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(int len$326, unsigned long long *l$328)
{
  int pc$330;
  unsigned long long ins$332;
  unsigned char op$334;
  unsigned char opc;
  unsigned int dst$338;
  unsigned long long dst64$340;
  _Bool is_imm;
  int imm$344;
  unsigned long long imm64;
  unsigned int src;
  unsigned long long src64$350;
  unsigned int dst$352;
  unsigned long long dst64$354;
  unsigned int dst32$356;
  _Bool is_imm$358;
  int imm$360;
  unsigned int src$362;
  unsigned long long src64$364;
  unsigned int src32$366;
  unsigned int dst$368;
  unsigned long long dst64$370;
  int ofs$372;
  _Bool is_imm$374;
  int imm$376;
  unsigned long long imm64$378;
  unsigned int src$380;
  unsigned long long src64$382;
  unsigned int dst$384;
  unsigned long long dst64$386;
  int imm$388;
  unsigned int dst$390;
  unsigned long long dst64$392;
  unsigned int src$394;
  unsigned long long src64$396;
  int ofs$398;
  unsigned long long ofs64$400;
  unsigned long long addr$402;
  unsigned int dst$404;
  unsigned long long dst64$406;
  int ofs$408;
  unsigned long long ofs64$410;
  int imm$412;
  unsigned long long addr$414;
  unsigned int dst$416;
  unsigned long long dst64$418;
  unsigned int src$420;
  unsigned long long src64$422;
  int ofs$424;
  unsigned long long ofs64$426;
  unsigned long long addr$428;
  pc$330 = eval_pc();
  ins$332 = list_get(l$328, pc$330);
  op$334 = get_opcode_ins(ins$332);
  opc = get_opcode(op$334);
  switch (opc) {
    case 7:
      dst$338 = get_dst(ins$332);
      dst64$340 = eval_reg(dst$338);
      is_imm = comp_and_0x08_byte(op$334);
      if (is_imm) {
        imm$344 = get_immediate(ins$332);
        imm64 = eval_immediate(imm$344);
        step_opcode_alu64(dst$338, dst64$340, imm64, op$334);
        return;
      } else {
        src = get_src(ins$332);
        src64$350 = eval_reg(src);
        step_opcode_alu64(dst$338, dst64$340, src64$350, op$334);
        return;
      }
    case 4:
      dst$352 = get_dst(ins$332);
      dst64$354 = eval_reg(dst$352);
      dst32$356 = reg64_to_reg32(dst64$354);
      is_imm$358 = comp_and_0x08_byte(op$334);
      if (is_imm$358) {
        imm$360 = get_immediate(ins$332);
        step_opcode_alu32(dst$352, dst32$356, imm$360, op$334);
        return;
      } else {
        src$362 = get_src(ins$332);
        src64$364 = eval_reg(src$362);
        src32$366 = reg64_to_reg32(src64$364);
        step_opcode_alu32(dst$352, dst32$356, src32$366, op$334);
        return;
      }
    case 5:
      dst$368 = get_dst(ins$332);
      dst64$370 = eval_reg(dst$368);
      ofs$372 = get_offset(ins$332);
      is_imm$374 = comp_and_0x08_byte(op$334);
      if (is_imm$374) {
        imm$376 = get_immediate(ins$332);
        imm64$378 = eval_immediate(imm$376);
        step_opcode_branch(pc$330, ofs$372, dst64$370, imm64$378, op$334);
        return;
      } else {
        src$380 = get_src(ins$332);
        src64$382 = eval_reg(src$380);
        step_opcode_branch(pc$330, ofs$372, dst64$370, src64$382, op$334);
        return;
      }
    case 0:
      dst$384 = get_dst(ins$332);
      dst64$386 = eval_reg(dst$384);
      imm$388 = get_immediate(ins$332);
      step_opcode_mem_ld_imm(pc$330, len$326, dst$384, dst64$386, imm$388,
                             op$334, l$328);
      return;
    case 1:
      dst$390 = get_dst(ins$332);
      dst64$392 = eval_reg(dst$390);
      src$394 = get_src(ins$332);
      src64$396 = eval_reg(src$394);
      ofs$398 = get_offset(ins$332);
      ofs64$400 = eval_immediate(ofs$398);
      addr$402 = get_addl(src64$396, ofs64$400);
      step_opcode_mem_ld_reg(pc$330, dst$390, dst64$392, src64$396, op$334,
                             ofs64$400, addr$402);
      return;
    case 2:
      dst$404 = get_dst(ins$332);
      dst64$406 = eval_reg(dst$404);
      ofs$408 = get_offset(ins$332);
      ofs64$410 = eval_immediate(ofs$408);
      imm$412 = get_immediate(ins$332);
      addr$414 = get_addl(dst64$406, ofs64$410);
      step_opcode_mem_st_imm(pc$330, dst$404, dst64$406, imm$412, op$334,
                             ofs64$410, addr$414);
      return;
    case 3:
      dst$416 = get_dst(ins$332);
      dst64$418 = eval_reg(dst$416);
      src$420 = get_src(ins$332);
      src64$422 = eval_reg(src$420);
      ofs$424 = get_offset(ins$332);
      ofs64$426 = eval_immediate(ofs$424);
      addr$428 = get_addl(dst64$418, ofs64$426);
      step_opcode_mem_st_reg(pc$330, dst$416, dst64$418, src64$422, op$334,
                             ofs64$426, addr$428);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(int len$430, unsigned int fuel, unsigned long long *l$434)
{
  unsigned int fuel0;
  int pc$438;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    pc$438 = eval_pc();
    if (0U <= pc$438 && pc$438 < len$430) {
      step(len$430, l$434);
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
        bpf_interpreter_aux(len$430, fuel0, l$434);
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

unsigned long long bpf_interpreter(int len$442, unsigned int fuel$444, unsigned long long *l$446)
{
  struct memory_region *bpf_ctx;
  int f$450;
  bpf_ctx = get_mem_region(0U);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(len$442, fuel$444, l$446);
  f$450 = eval_flag();
  if (f$450 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


