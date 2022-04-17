struct memory_region;
struct bpf_state;
struct memory_region {
  unsigned int start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned char *block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned long long regsmap[11];
  unsigned int mrs_num;
  struct memory_region *mrs$757165;
  unsigned int ins_len;
  unsigned long long *ins$756645;
};

extern unsigned int reg64_to_reg32(unsigned long long);

extern int get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern long long eval_immediate(int);

extern unsigned long long get_src64(unsigned char, unsigned long long);

extern unsigned int get_src32(unsigned char, unsigned long long);

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

extern unsigned int get_start_addr(struct memory_region *);

extern unsigned int get_block_size(struct memory_region *);

extern unsigned int get_block_perm(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned char *check_mem_aux2(struct memory_region *, unsigned int, unsigned int, unsigned int);

extern unsigned char *check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned int, struct memory_region *);

extern unsigned char *check_mem(unsigned int, unsigned int, unsigned int);

extern void step_opcode_alu64(unsigned long long, unsigned long long, unsigned int, unsigned char);

extern void step_opcode_alu32(unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_branch(unsigned long long, unsigned long long, unsigned int, unsigned int, unsigned char);

extern void step_opcode_mem_ld_imm(int, unsigned long long, unsigned int, unsigned int, unsigned char);

extern void step_opcode_mem_ld_reg(unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_mem_st_imm(int, unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_mem_st_reg(unsigned long long, unsigned int, unsigned int, unsigned int, unsigned char);

extern void step(void);

extern void bpf_interpreter_aux(unsigned int);

extern unsigned long long bpf_interpreter(unsigned int);

extern unsigned int eval_pc(void);

extern void upd_pc(unsigned int);

extern void upd_pc_incr(void);

extern int eval_flag(void);

extern void upd_flag(int);

extern unsigned int eval_mrs_num(void);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern struct memory_region *eval_mrs_regions(void);

extern unsigned long long load_mem(unsigned int, unsigned int);

extern void store_mem_imm(unsigned char *, unsigned int, int);

extern void store_mem_reg(unsigned char *, unsigned int, unsigned long long);

extern unsigned int eval_ins_len(void);

extern unsigned long long eval_ins(unsigned int);

extern _Bool cmp_ptr32_nullM(unsigned char *);

extern unsigned int get_dst(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern struct memory_region *get_mem_region(unsigned int, struct memory_region *);

extern unsigned char *_bpf_get_call(int);

extern unsigned int exec_function(unsigned char *);

unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

int get_offset(unsigned long long ins)
{
  return (int) (short) (ins << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins$116)
{
  return (int) (ins$116 >> 32LLU);
}

long long eval_immediate(int ins$118)
{
  return (long long) ins$118;
}

unsigned long long get_src64(unsigned char x, unsigned long long ins$122)
{
  int imm;
  long long imm64;
  unsigned int src;
  unsigned long long src64;
  if (0U == (x & 8U)) {
    imm = get_immediate(ins$122);
    imm64 = eval_immediate(imm);
    return (unsigned long long) imm64;
  } else {
    src = get_src(ins$122);
    src64 = eval_reg(src);
    return src64;
  }
}

unsigned int get_src32(unsigned char x$132, unsigned long long ins$134)
{
  int imm$136;
  unsigned int src$138;
  unsigned long long src64$140;
  unsigned int src32;
  if (0U == (x$132 & 8U)) {
    imm$136 = get_immediate(ins$134);
    return imm$136;
  } else {
    src$138 = get_src(ins$134);
    src64$140 = eval_reg(src$138);
    src32 = reg64_to_reg32(src64$140);
    return src32;
  }
}

unsigned char get_opcode_ins(unsigned long long ins$144)
{
  return (unsigned char) (ins$144 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$148)
{
  return (unsigned char) (op$148 & 240);
}

unsigned char get_opcode_branch(unsigned char op$150)
{
  return (unsigned char) (op$150 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$152)
{
  return (unsigned char) (op$152 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$154)
{
  return (unsigned char) (op$154 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$156)
{
  return (unsigned char) (op$156 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$158)
{
  return (unsigned char) (op$158 & 255);
}

unsigned char get_opcode(unsigned char op$160)
{
  return (unsigned char) (op$160 & 7);
}

unsigned int get_add(unsigned int x$162, unsigned int y)
{
  return x$162 + y;
}

unsigned int get_sub(unsigned int x$166, unsigned int y$168)
{
  return x$166 - y$168;
}

unsigned int get_addr_ofs(unsigned long long x$170, int ofs)
{
  return (unsigned int) (x$170 + (unsigned long long) ofs);
}

unsigned int get_start_addr(struct memory_region *mr)
{
  return (*mr).start_addr;
}

unsigned int get_block_size(struct memory_region *mr$176)
{
  return (*mr$176).block_size;
}

unsigned int get_block_perm(struct memory_region *mr$178)
{
  return (*mr$178).block_perm;
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

unsigned char *check_mem_aux2(struct memory_region *mr$182, unsigned int perm, unsigned int addr, unsigned int chunk$188)
{
  unsigned int start;
  unsigned int size;
  unsigned int mr_perm;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  start = get_start_addr(mr$182);
  size = get_block_size(mr$182);
  mr_perm = get_block_perm(mr$182);
  lo_ofs = get_sub(addr, start);
  hi_ofs = get_add(lo_ofs, chunk$188);
  if (hi_ofs < size
        && (lo_ofs <= 4294967295U - chunk$188 && 0U == lo_ofs % chunk$188)
        && mr_perm >= perm) {
    return (*mr$182).block_ptr + lo_ofs;
  } else {
    return 0;
  }
}

unsigned char *check_mem_aux(unsigned int num, unsigned int perm$202, unsigned int chunk$204, unsigned int addr$206, struct memory_region *mrs)
{
  unsigned int n;
  struct memory_region *cur_mr;
  unsigned char *check_mem$214;
  _Bool is_null;
  if (num == 0U) {
    return 0;
  } else {
    n = num - 1U;
    cur_mr = get_mem_region(n, mrs);
    check_mem$214 = check_mem_aux2(cur_mr, perm$202, addr$206, chunk$204);
    is_null = cmp_ptr32_nullM(check_mem$214);
    if (is_null) {
      return check_mem_aux(n, perm$202, chunk$204, addr$206, mrs);
    } else {
      return check_mem$214;
    }
  }
}

unsigned char *check_mem(unsigned int perm$218, unsigned int chunk$220, unsigned int addr$222)
{
  _Bool well_chunk;
  unsigned int mem_reg_num;
  struct memory_region *mrs$228;
  unsigned char *check_mem$230;
  _Bool is_null$232;
  well_chunk = is_well_chunk_bool(chunk$220);
  if (well_chunk) {
    mem_reg_num = eval_mrs_num();
    mrs$228 = eval_mrs_regions();
    check_mem$230 =
      check_mem_aux(mem_reg_num, perm$218, chunk$220, addr$222, mrs$228);
    is_null$232 = cmp_ptr32_nullM(check_mem$230);
    if (is_null$232) {
      return 0;
    } else {
      return check_mem$230;
    }
  } else {
    return 0;
  }
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64$236, unsigned int dst, unsigned char op$240)
{
  unsigned char opcode_alu64;
  unsigned int src32$244;
  unsigned int src32$246;
  unsigned int src32$248;
  opcode_alu64 = get_opcode_alu64(op$240);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64$236);
      return;
    case 16:
      upd_reg(dst, dst64 - src64$236);
      return;
    case 32:
      upd_reg(dst, dst64 * src64$236);
      return;
    case 48:
      if (src64$236 != 0LLU) {
        upd_reg(dst, dst64 / src64$236);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64$236);
      return;
    case 80:
      upd_reg(dst, dst64 & src64$236);
      return;
    case 96:
      src32$244 = reg64_to_reg32(src64$236);
      if (src32$244 < 64U) {
        upd_reg(dst, dst64 << src32$244);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32$246 = reg64_to_reg32(src64$236);
      if (src32$246 < 64U) {
        upd_reg(dst, dst64 >> src32$246);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$240 == 135) {
        upd_reg(dst, -dst64);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src64$236 != 0LLU) {
        upd_reg(dst, dst64 % src64$236);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64$236);
      return;
    case 176:
      upd_reg(dst, src64$236);
      return;
    case 192:
      src32$248 = reg64_to_reg32(src64$236);
      if (src32$248 < 64U) {
        upd_reg(dst, (unsigned long long) ((long long) dst64 >> src32$248));
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$252, unsigned int dst$254, unsigned char op$256)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$256);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$254, (unsigned long long) (dst32 + src32$252));
      return;
    case 16:
      upd_reg(dst$254, (unsigned long long) (dst32 - src32$252));
      return;
    case 32:
      upd_reg(dst$254, (unsigned long long) (dst32 * src32$252));
      return;
    case 48:
      if (src32$252 != 0U) {
        upd_reg(dst$254, (unsigned long long) (dst32 / src32$252));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$254, (unsigned long long) (dst32 | src32$252));
      return;
    case 80:
      upd_reg(dst$254, (unsigned long long) (dst32 & src32$252));
      return;
    case 96:
      if (src32$252 < 32U) {
        upd_reg(dst$254, (unsigned long long) (dst32 << src32$252));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$252 < 32U) {
        upd_reg(dst$254, (unsigned long long) (dst32 >> src32$252));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$256 == 132) {
        upd_reg(dst$254, (unsigned long long) -dst32);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src32$252 != 0U) {
        upd_reg(dst$254, (unsigned long long) (dst32 % src32$252));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$254, (unsigned long long) (dst32 ^ src32$252));
      return;
    case 176:
      upd_reg(dst$254, (unsigned long long) src32$252);
      return;
    case 192:
      if (src32$252 < 32U) {
        upd_reg(dst$254, (unsigned long long) ((int) dst32 >> src32$252));
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

void step_opcode_branch(unsigned long long dst64$260, unsigned long long src64$262, unsigned int pc, unsigned int ofs$266, unsigned char op$268)
{
  unsigned char opcode_jmp;
  unsigned char *f_ptr;
  _Bool is_null$274;
  unsigned int res;
  opcode_jmp = get_opcode_branch(op$268);
  switch (opcode_jmp) {
    case 0:
      if (op$268 == 5) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 16:
      if (dst64$260 == src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 32:
      if (dst64$260 > src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 48:
      if (dst64$260 >= src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 160:
      if (dst64$260 < src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 176:
      if (dst64$260 <= src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 64:
      if ((dst64$260 & src64$262) != 0LLU) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 80:
      if (dst64$260 != src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 96:
      if ((long long) dst64$260 > (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 112:
      if ((long long) dst64$260 >= (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 192:
      if ((long long) dst64$260 < (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 208:
      if ((long long) dst64$260 <= (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 128:
      if (op$268 == 133) {
        f_ptr = _bpf_get_call((int) src64$262);
        is_null$274 = cmp_ptr32_nullM(f_ptr);
        if (is_null$274) {
          upd_flag(-4);
          return;
        } else {
          res = exec_function(f_ptr);
          upd_reg(0U, (unsigned long long) res);
          return;
        }
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (op$268 == 149) {
        upd_flag(1);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_imm(int imm$278, unsigned long long dst64$280, unsigned int pc$282, unsigned int dst$284, unsigned char op$286)
{
  unsigned char opcode_ld;
  opcode_ld = get_opcode_mem_ld_imm(op$286);
  switch (opcode_ld) {
    case 24:
      upd_reg(dst$284, (unsigned long long) imm$278);
      return;
    case 16:
      upd_reg(dst$284, dst64$280 | (unsigned long long) imm$278 << 32U);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_reg(unsigned int addr$290, unsigned int pc$292, unsigned int dst$294, unsigned char op$296)
{
  unsigned char opcode_ld$298;
  unsigned char *addr_ptr;
  _Bool is_null$302;
  unsigned long long v;
  unsigned char *addr_ptr$306;
  _Bool is_null$308;
  unsigned long long v$310;
  unsigned char *addr_ptr$312;
  _Bool is_null$314;
  unsigned long long v$316;
  unsigned char *addr_ptr$318;
  _Bool is_null$320;
  unsigned long long v$322;
  opcode_ld$298 = get_opcode_mem_ld_reg(op$296);
  switch (opcode_ld$298) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$290);
      is_null$302 = cmp_ptr32_nullM(addr_ptr);
      if (is_null$302) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$294, v);
        return;
      }
    case 105:
      addr_ptr$306 = check_mem(1U, 2U, addr$290);
      is_null$308 = cmp_ptr32_nullM(addr_ptr$306);
      if (is_null$308) {
        upd_flag(-2);
        return;
      } else {
        v$310 = load_mem(2U, addr_ptr$306);
        upd_reg(dst$294, v$310);
        return;
      }
    case 113:
      addr_ptr$312 = check_mem(1U, 1U, addr$290);
      is_null$314 = cmp_ptr32_nullM(addr_ptr$312);
      if (is_null$314) {
        upd_flag(-2);
        return;
      } else {
        v$316 = load_mem(1U, addr_ptr$312);
        upd_reg(dst$294, v$316);
        return;
      }
    case 121:
      addr_ptr$318 = check_mem(1U, 8U, addr$290);
      is_null$320 = cmp_ptr32_nullM(addr_ptr$318);
      if (is_null$320) {
        upd_flag(-2);
        return;
      } else {
        v$322 = load_mem(8U, addr_ptr$318);
        upd_reg(dst$294, v$322);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$324, unsigned int addr$326, unsigned int pc$328, unsigned int dst$330, unsigned char op$332)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$336;
  _Bool is_null$338;
  unsigned char *addr_ptr$340;
  _Bool is_null$342;
  unsigned char *addr_ptr$344;
  _Bool is_null$346;
  unsigned char *addr_ptr$348;
  _Bool is_null$350;
  opcode_st = get_opcode_mem_st_imm(op$332);
  switch (opcode_st) {
    case 98:
      addr_ptr$336 = check_mem(2U, 4U, addr$326);
      is_null$338 = cmp_ptr32_nullM(addr_ptr$336);
      if (is_null$338) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$336, 4U, imm$324);
        return;
      }
    case 106:
      addr_ptr$340 = check_mem(2U, 2U, addr$326);
      is_null$342 = cmp_ptr32_nullM(addr_ptr$340);
      if (is_null$342) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$340, 2U, imm$324);
        return;
      }
    case 114:
      addr_ptr$344 = check_mem(2U, 1U, addr$326);
      is_null$346 = cmp_ptr32_nullM(addr_ptr$344);
      if (is_null$346) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$344, 1U, imm$324);
        return;
      }
    case 122:
      addr_ptr$348 = check_mem(2U, 8U, addr$326);
      is_null$350 = cmp_ptr32_nullM(addr_ptr$348);
      if (is_null$350) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$348, 8U, imm$324);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$352, unsigned int addr$354, unsigned int pc$356, unsigned int dst$358, unsigned char op$360)
{
  unsigned char opcode_st$362;
  unsigned char *addr_ptr$364;
  _Bool is_null$366;
  unsigned char *addr_ptr$368;
  _Bool is_null$370;
  unsigned char *addr_ptr$372;
  _Bool is_null$374;
  unsigned char *addr_ptr$376;
  _Bool is_null$378;
  opcode_st$362 = get_opcode_mem_st_reg(op$360);
  switch (opcode_st$362) {
    case 99:
      addr_ptr$364 = check_mem(2U, 4U, addr$354);
      is_null$366 = cmp_ptr32_nullM(addr_ptr$364);
      if (is_null$366) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$364, 4U, src64$352);
        return;
      }
    case 107:
      addr_ptr$368 = check_mem(2U, 2U, addr$354);
      is_null$370 = cmp_ptr32_nullM(addr_ptr$368);
      if (is_null$370) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$368, 2U, src64$352);
        return;
      }
    case 115:
      addr_ptr$372 = check_mem(2U, 1U, addr$354);
      is_null$374 = cmp_ptr32_nullM(addr_ptr$372);
      if (is_null$374) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$372, 1U, src64$352);
        return;
      }
    case 123:
      addr_ptr$376 = check_mem(2U, 8U, addr$354);
      is_null$378 = cmp_ptr32_nullM(addr_ptr$376);
      if (is_null$378) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$376, 8U, src64$352);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  unsigned int pc$380;
  unsigned long long ins$382;
  unsigned char op$384;
  unsigned char opc;
  unsigned int dst$388;
  unsigned long long dst64$390;
  unsigned long long src64$392;
  unsigned long long dst64$394;
  unsigned int dst32$396;
  unsigned int src32$398;
  unsigned long long dst64$400;
  int ofs$402;
  unsigned long long src64$404;
  unsigned long long dst64$406;
  int imm$408;
  unsigned int src$410;
  unsigned long long src64$412;
  int ofs$414;
  unsigned int addr$416;
  unsigned long long dst64$418;
  int ofs$420;
  int imm$422;
  unsigned int addr$424;
  unsigned long long dst64$426;
  unsigned int src$428;
  unsigned long long src64$430;
  int ofs$432;
  unsigned int addr$434;
  pc$380 = eval_pc();
  ins$382 = eval_ins(pc$380);
  op$384 = get_opcode_ins(ins$382);
  opc = get_opcode(op$384);
  dst$388 = get_dst(ins$382);
  switch (opc) {
    case 7:
      dst64$390 = eval_reg(dst$388);
      src64$392 = get_src64(op$384, ins$382);
      step_opcode_alu64(dst64$390, src64$392, dst$388, op$384);
      return;
    case 4:
      dst64$394 = eval_reg(dst$388);
      dst32$396 = reg64_to_reg32(dst64$394);
      src32$398 = get_src32(op$384, ins$382);
      step_opcode_alu32(dst32$396, src32$398, dst$388, op$384);
      return;
    case 5:
      dst64$400 = eval_reg(dst$388);
      ofs$402 = get_offset(ins$382);
      src64$404 = get_src64(op$384, ins$382);
      step_opcode_branch(dst64$400, src64$404, pc$380,
                         (unsigned int) ofs$402, op$384);
      return;
    case 0:
      dst64$406 = eval_reg(dst$388);
      imm$408 = get_immediate(ins$382);
      step_opcode_mem_ld_imm(imm$408, dst64$406, pc$380, dst$388, op$384);
      return;
    case 1:
      src$410 = get_src(ins$382);
      src64$412 = eval_reg(src$410);
      ofs$414 = get_offset(ins$382);
      addr$416 = get_addr_ofs(src64$412, ofs$414);
      step_opcode_mem_ld_reg(addr$416, pc$380, dst$388, op$384);
      return;
    case 2:
      dst64$418 = eval_reg(dst$388);
      ofs$420 = get_offset(ins$382);
      imm$422 = get_immediate(ins$382);
      addr$424 = get_addr_ofs(dst64$418, ofs$420);
      step_opcode_mem_st_imm(imm$422, addr$424, pc$380, dst$388, op$384);
      return;
    case 3:
      dst64$426 = eval_reg(dst$388);
      src$428 = get_src(ins$382);
      src64$430 = eval_reg(src$428);
      ofs$432 = get_offset(ins$382);
      addr$434 = get_addr_ofs(dst64$426, ofs$432);
      step_opcode_mem_st_reg(src64$430, addr$434, pc$380, dst$388, op$384);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  unsigned int len;
  unsigned int pc$442;
  int f;
  unsigned int len0;
  unsigned int pc0;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len = eval_ins_len();
    pc$442 = eval_pc();
    if (pc$442 < len) {
      step();
      f = eval_flag();
      if (f == 0) {
        len0 = eval_ins_len();
        pc0 = eval_pc();
        if (pc0 + 1U < len0) {
          upd_pc_incr();
          bpf_interpreter_aux(fuel0);
          return;
        } else {
          upd_flag(-5);
          return;
        }
      } else {
        return;
      }
    } else {
      upd_flag(-5);
      return;
    }
  }
}

unsigned long long bpf_interpreter(unsigned int fuel$450)
{
  struct memory_region *mrs$452;
  struct memory_region *bpf_ctx;
  unsigned int start$456;
  int f$458;
  unsigned long long res$460;
  mrs$452 = eval_mrs_regions();
  bpf_ctx = get_mem_region(0U, mrs$452);
  start$456 = get_start_addr(bpf_ctx);
  upd_reg(1U, (unsigned long long) start$456);
  bpf_interpreter_aux(fuel$450);
  f$458 = eval_flag();
  if (f$458 == 1) {
    res$460 = eval_reg(0U);
    return res$460;
  } else {
    return 0LLU;
  }
}


