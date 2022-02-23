struct memory_region;
struct bpf_state;
struct memory_region {
  unsigned int start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned char *block_ptr;
};

struct bpf_state {
  int state_pc;
  int bpf_flag;
  unsigned long long regsmap[11];
  unsigned int mrs_num;
  struct memory_region *mrs$757165;
  int ins_len;
  unsigned long long *ins$756645;
};

extern struct memory_region *get_mem_region(unsigned int, struct memory_region *);

extern unsigned int get_dst(unsigned long long);

extern unsigned int reg64_to_reg32(unsigned long long);

extern unsigned int get_src(unsigned long long);

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

extern void step_opcode_branch(unsigned long long, unsigned long long, int, int, unsigned char);

extern void step_opcode_mem_ld_imm(int, int, unsigned int, unsigned char);

extern void step_opcode_mem_ld_reg(unsigned int, int, unsigned int, unsigned char);

extern void step_opcode_mem_st_imm(int, unsigned int, int, unsigned int, unsigned char);

extern void step_opcode_mem_st_reg(unsigned long long, unsigned int, int, unsigned int, unsigned char);

extern void step(void);

extern void bpf_interpreter_aux(unsigned int);

extern unsigned long long bpf_interpreter(unsigned int);

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

extern int eval_ins_len(void);

extern unsigned long long eval_ins(int);

extern _Bool cmp_ptr32_nullM(unsigned char *);

extern unsigned char *_bpf_get_call(int);

extern unsigned int exec_function(unsigned char *);

struct memory_region *get_mem_region(unsigned int n, struct memory_region *mrs)
{
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

unsigned int get_src(unsigned long long ins$120)
{
  return (unsigned int) ((ins$120 & 65535LLU) >> 12LLU);
}

int get_offset(unsigned long long ins$122)
{
  return (int) (short) (ins$122 << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins$124)
{
  return (int) (ins$124 >> 32LLU);
}

long long eval_immediate(int ins$126)
{
  return (long long) ins$126;
}

unsigned long long get_src64(unsigned char x, unsigned long long ins$130)
{
  int imm;
  long long imm64;
  unsigned int src;
  unsigned long long src64;
  if (0U == (x & 8)) {
    imm = get_immediate(ins$130);
    imm64 = eval_immediate(imm);
    return (unsigned long long) imm64;
  } else {
    src = get_src(ins$130);
    src64 = eval_reg(src);
    return src64;
  }
}

unsigned int get_src32(unsigned char x$140, unsigned long long ins$142)
{
  int imm$144;
  unsigned int src$146;
  unsigned long long src64$148;
  unsigned int src32;
  if (0U == (x$140 & 8)) {
    imm$144 = get_immediate(ins$142);
    return imm$144;
  } else {
    src$146 = get_src(ins$142);
    src64$148 = eval_reg(src$146);
    src32 = reg64_to_reg32(src64$148);
    return src32;
  }
}

unsigned char get_opcode_ins(unsigned long long ins$152)
{
  return (unsigned char) (ins$152 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$156)
{
  return (unsigned char) (op$156 & 240);
}

unsigned char get_opcode_branch(unsigned char op$158)
{
  return (unsigned char) (op$158 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$160)
{
  return (unsigned char) (op$160 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$162)
{
  return (unsigned char) (op$162 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$164)
{
  return (unsigned char) (op$164 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$166)
{
  return (unsigned char) (op$166 & 255);
}

unsigned char get_opcode(unsigned char op$168)
{
  return (unsigned char) (op$168 & 7);
}

unsigned int get_add(unsigned int x$170, unsigned int y)
{
  return x$170 + y;
}

unsigned int get_sub(unsigned int x$174, unsigned int y$176)
{
  return x$174 - y$176;
}

unsigned int get_addr_ofs(unsigned long long x$178, int ofs)
{
  return (unsigned int) (x$178 + (unsigned long long) ofs);
}

unsigned int get_start_addr(struct memory_region *mr)
{
  return (*mr).start_addr;
}

unsigned int get_block_size(struct memory_region *mr$184)
{
  return (*mr$184).block_size;
}

unsigned int get_block_perm(struct memory_region *mr$186)
{
  return (*mr$186).block_perm;
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

unsigned char *check_mem_aux2(struct memory_region *mr$190, unsigned int perm, unsigned int addr, unsigned int chunk$196)
{
  unsigned int start;
  unsigned int size;
  unsigned int mr_perm;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  start = get_start_addr(mr$190);
  size = get_block_size(mr$190);
  mr_perm = get_block_perm(mr$190);
  lo_ofs = get_sub(addr, start);
  hi_ofs = get_add(lo_ofs, chunk$196);
  if (hi_ofs < size
        && (lo_ofs <= 4294967295U - chunk$196 && 0U == lo_ofs % chunk$196)
        && mr_perm >= perm) {
    return (*mr$190).block_ptr + lo_ofs;
  } else {
    return 0;
  }
}

unsigned char *check_mem_aux(unsigned int num, unsigned int perm$210, unsigned int chunk$212, unsigned int addr$214, struct memory_region *mrs$216)
{
  unsigned int n$218;
  struct memory_region *cur_mr;
  unsigned char *check_mem$222;
  _Bool is_null;
  if (num == 0U) {
    return 0;
  } else {
    n$218 = num - 1U;
    cur_mr = get_mem_region(n$218, mrs$216);
    check_mem$222 = check_mem_aux2(cur_mr, perm$210, addr$214, chunk$212);
    is_null = cmp_ptr32_nullM(check_mem$222);
    if (is_null) {
      return check_mem_aux(n$218, perm$210, chunk$212, addr$214, mrs$216);
    } else {
      return check_mem$222;
    }
  }
}

unsigned char *check_mem(unsigned int perm$226, unsigned int chunk$228, unsigned int addr$230)
{
  _Bool well_chunk;
  unsigned int mem_reg_num;
  struct memory_region *mrs$236;
  unsigned char *check_mem$238;
  _Bool is_null$240;
  well_chunk = is_well_chunk_bool(chunk$228);
  if (well_chunk) {
    mem_reg_num = eval_mrs_num();
    mrs$236 = eval_mrs_regions();
    check_mem$238 =
      check_mem_aux(mem_reg_num, perm$226, chunk$228, addr$230, mrs$236);
    is_null$240 = cmp_ptr32_nullM(check_mem$238);
    if (is_null$240) {
      return 0;
    } else {
      return check_mem$238;
    }
  } else {
    return 0;
  }
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64$244, unsigned int dst, unsigned char op$248)
{
  unsigned char opcode_alu64;
  unsigned int src32$252;
  unsigned int src32$254;
  unsigned int src32$256;
  opcode_alu64 = get_opcode_alu64(op$248);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64$244);
      return;
    case 16:
      upd_reg(dst, dst64 - src64$244);
      return;
    case 32:
      upd_reg(dst, dst64 * src64$244);
      return;
    case 48:
      if (src64$244 != 0LLU) {
        upd_reg(dst, dst64 / src64$244);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64$244);
      return;
    case 80:
      upd_reg(dst, dst64 & src64$244);
      return;
    case 96:
      src32$252 = reg64_to_reg32(src64$244);
      if (src32$252 < 64U) {
        upd_reg(dst, dst64 << src32$252);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32$254 = reg64_to_reg32(src64$244);
      if (src32$254 < 64U) {
        upd_reg(dst, dst64 >> src32$254);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$248 == 135) {
        upd_reg(dst, -dst64);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src64$244 != 0LLU) {
        upd_reg(dst, dst64 % src64$244);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64$244);
      return;
    case 176:
      upd_reg(dst, src64$244);
      return;
    case 192:
      src32$256 = reg64_to_reg32(src64$244);
      if (src32$256 < 64U) {
        upd_reg(dst, (unsigned long long) ((long long) dst64 >> src32$256));
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$260, unsigned int dst$262, unsigned char op$264)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$264);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$262, (unsigned long long) (dst32 + src32$260));
      return;
    case 16:
      upd_reg(dst$262, (unsigned long long) (dst32 - src32$260));
      return;
    case 32:
      upd_reg(dst$262, (unsigned long long) (dst32 * src32$260));
      return;
    case 48:
      if (src32$260 != 0U) {
        upd_reg(dst$262, (unsigned long long) (dst32 / src32$260));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$262, (unsigned long long) (dst32 | src32$260));
      return;
    case 80:
      upd_reg(dst$262, (unsigned long long) (dst32 & src32$260));
      return;
    case 96:
      if (src32$260 < 32U) {
        upd_reg(dst$262, (unsigned long long) (dst32 << src32$260));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$260 < 32U) {
        upd_reg(dst$262, (unsigned long long) (dst32 >> src32$260));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$264 == 132) {
        upd_reg(dst$262, (unsigned long long) -dst32);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src32$260 != 0U) {
        upd_reg(dst$262, (unsigned long long) (dst32 % src32$260));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$262, (unsigned long long) (dst32 ^ src32$260));
      return;
    case 176:
      upd_reg(dst$262, (unsigned long long) src32$260);
      return;
    case 192:
      if (src32$260 < 32U) {
        upd_reg(dst$262, (unsigned long long) ((int) dst32 >> src32$260));
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

void step_opcode_branch(unsigned long long dst64$268, unsigned long long src64$270, int pc, int ofs$274, unsigned char op$276)
{
  unsigned char opcode_jmp;
  unsigned char *f_ptr;
  _Bool is_null$282;
  unsigned int res;
  opcode_jmp = get_opcode_branch(op$276);
  switch (opcode_jmp) {
    case 0:
      if (op$276 == 5) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 16:
      if (dst64$268 == src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 32:
      if (dst64$268 > src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 48:
      if (dst64$268 >= src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 160:
      if (dst64$268 < src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 176:
      if (dst64$268 <= src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 64:
      if ((dst64$268 & src64$270) != 0LLU) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 80:
      if (dst64$268 != src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 96:
      if ((long long) dst64$268 > (long long) src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 112:
      if ((long long) dst64$268 >= (long long) src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 192:
      if ((long long) dst64$268 < (long long) src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 208:
      if ((long long) dst64$268 <= (long long) src64$270) {
        upd_pc(pc + ofs$274);
        return;
      } else {
        return;
      }
    case 128:
      if (op$276 == 133) {
        f_ptr = _bpf_get_call((int) src64$270);
        is_null$282 = cmp_ptr32_nullM(f_ptr);
        if (is_null$282) {
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
      if (op$276 == 149) {
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

void step_opcode_mem_ld_imm(int imm$286, int pc$288, unsigned int dst$290, unsigned char op$292)
{
  int len;
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  len = eval_ins_len();
  opcode_ld = get_opcode_mem_ld_imm(op$292);
  switch (opcode_ld) {
    case 24:
      if (pc$288 + 1 < len) {
        next_ins = eval_ins(pc$288 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$290,
                (unsigned long long) imm$286
                  | (unsigned long long) next_imm << 32U);
        upd_pc_incr();
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

void step_opcode_mem_ld_reg(unsigned int addr$302, int pc$304, unsigned int dst$306, unsigned char op$308)
{
  unsigned char opcode_ld$310;
  unsigned char *addr_ptr;
  _Bool is_null$314;
  unsigned long long v;
  unsigned char *addr_ptr$318;
  _Bool is_null$320;
  unsigned long long v$322;
  unsigned char *addr_ptr$324;
  _Bool is_null$326;
  unsigned long long v$328;
  unsigned char *addr_ptr$330;
  _Bool is_null$332;
  unsigned long long v$334;
  opcode_ld$310 = get_opcode_mem_ld_reg(op$308);
  switch (opcode_ld$310) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$302);
      is_null$314 = cmp_ptr32_nullM(addr_ptr);
      if (is_null$314) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$306, v);
        return;
      }
    case 105:
      addr_ptr$318 = check_mem(1U, 2U, addr$302);
      is_null$320 = cmp_ptr32_nullM(addr_ptr$318);
      if (is_null$320) {
        upd_flag(-2);
        return;
      } else {
        v$322 = load_mem(2U, addr_ptr$318);
        upd_reg(dst$306, v$322);
        return;
      }
    case 113:
      addr_ptr$324 = check_mem(1U, 1U, addr$302);
      is_null$326 = cmp_ptr32_nullM(addr_ptr$324);
      if (is_null$326) {
        upd_flag(-2);
        return;
      } else {
        v$328 = load_mem(1U, addr_ptr$324);
        upd_reg(dst$306, v$328);
        return;
      }
    case 121:
      addr_ptr$330 = check_mem(1U, 8U, addr$302);
      is_null$332 = cmp_ptr32_nullM(addr_ptr$330);
      if (is_null$332) {
        upd_flag(-2);
        return;
      } else {
        v$334 = load_mem(8U, addr_ptr$330);
        upd_reg(dst$306, v$334);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$336, unsigned int addr$338, int pc$340, unsigned int dst$342, unsigned char op$344)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$348;
  _Bool is_null$350;
  unsigned char *addr_ptr$352;
  _Bool is_null$354;
  unsigned char *addr_ptr$356;
  _Bool is_null$358;
  unsigned char *addr_ptr$360;
  _Bool is_null$362;
  opcode_st = get_opcode_mem_st_imm(op$344);
  switch (opcode_st) {
    case 98:
      addr_ptr$348 = check_mem(2U, 4U, addr$338);
      is_null$350 = cmp_ptr32_nullM(addr_ptr$348);
      if (is_null$350) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$348, imm$336);
        return;
      }
    case 106:
      addr_ptr$352 = check_mem(2U, 2U, addr$338);
      is_null$354 = cmp_ptr32_nullM(addr_ptr$352);
      if (is_null$354) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$352, imm$336);
        return;
      }
    case 114:
      addr_ptr$356 = check_mem(2U, 1U, addr$338);
      is_null$358 = cmp_ptr32_nullM(addr_ptr$356);
      if (is_null$358) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$356, imm$336);
        return;
      }
    case 122:
      addr_ptr$360 = check_mem(2U, 8U, addr$338);
      is_null$362 = cmp_ptr32_nullM(addr_ptr$360);
      if (is_null$362) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$360, imm$336);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$364, unsigned int addr$366, int pc$368, unsigned int dst$370, unsigned char op$372)
{
  unsigned char opcode_st$374;
  unsigned char *addr_ptr$376;
  _Bool is_null$378;
  unsigned char *addr_ptr$380;
  _Bool is_null$382;
  unsigned char *addr_ptr$384;
  _Bool is_null$386;
  unsigned char *addr_ptr$388;
  _Bool is_null$390;
  opcode_st$374 = get_opcode_mem_st_reg(op$372);
  switch (opcode_st$374) {
    case 99:
      addr_ptr$376 = check_mem(2U, 4U, addr$366);
      is_null$378 = cmp_ptr32_nullM(addr_ptr$376);
      if (is_null$378) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$376, src64$364);
        return;
      }
    case 107:
      addr_ptr$380 = check_mem(2U, 2U, addr$366);
      is_null$382 = cmp_ptr32_nullM(addr_ptr$380);
      if (is_null$382) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$380, src64$364);
        return;
      }
    case 115:
      addr_ptr$384 = check_mem(2U, 1U, addr$366);
      is_null$386 = cmp_ptr32_nullM(addr_ptr$384);
      if (is_null$386) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$384, src64$364);
        return;
      }
    case 123:
      addr_ptr$388 = check_mem(2U, 8U, addr$366);
      is_null$390 = cmp_ptr32_nullM(addr_ptr$388);
      if (is_null$390) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$388, src64$364);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  int pc$392;
  unsigned long long ins$394;
  unsigned char op$396;
  unsigned char opc;
  unsigned int dst$400;
  unsigned long long dst64$402;
  unsigned long long src64$404;
  unsigned long long dst64$406;
  unsigned int dst32$408;
  unsigned int src32$410;
  unsigned long long dst64$412;
  int ofs$414;
  unsigned long long src64$416;
  int imm$418;
  unsigned int src$420;
  unsigned long long src64$422;
  int ofs$424;
  unsigned int addr$426;
  unsigned long long dst64$428;
  int ofs$430;
  int imm$432;
  unsigned int addr$434;
  unsigned long long dst64$436;
  unsigned int src$438;
  unsigned long long src64$440;
  int ofs$442;
  unsigned int addr$444;
  pc$392 = eval_pc();
  ins$394 = eval_ins(pc$392);
  op$396 = get_opcode_ins(ins$394);
  opc = get_opcode(op$396);
  dst$400 = get_dst(ins$394);
  switch (opc) {
    case 7:
      dst64$402 = eval_reg(dst$400);
      src64$404 = get_src64(op$396, ins$394);
      step_opcode_alu64(dst64$402, src64$404, dst$400, op$396);
      return;
    case 4:
      dst64$406 = eval_reg(dst$400);
      dst32$408 = reg64_to_reg32(dst64$406);
      src32$410 = get_src32(op$396, ins$394);
      step_opcode_alu32(dst32$408, src32$410, dst$400, op$396);
      return;
    case 5:
      dst64$412 = eval_reg(dst$400);
      ofs$414 = get_offset(ins$394);
      src64$416 = get_src64(op$396, ins$394);
      step_opcode_branch(dst64$412, src64$416, pc$392, ofs$414, op$396);
      return;
    case 0:
      imm$418 = get_immediate(ins$394);
      step_opcode_mem_ld_imm(imm$418, pc$392, dst$400, op$396);
      return;
    case 1:
      src$420 = get_src(ins$394);
      src64$422 = eval_reg(src$420);
      ofs$424 = get_offset(ins$394);
      addr$426 = get_addr_ofs(src64$422, ofs$424);
      step_opcode_mem_ld_reg(addr$426, pc$392, dst$400, op$396);
      return;
    case 2:
      dst64$428 = eval_reg(dst$400);
      ofs$430 = get_offset(ins$394);
      imm$432 = get_immediate(ins$394);
      addr$434 = get_addr_ofs(dst64$428, ofs$430);
      step_opcode_mem_st_imm(imm$432, addr$434, pc$392, dst$400, op$396);
      return;
    case 3:
      dst64$436 = eval_reg(dst$400);
      src$438 = get_src(ins$394);
      src64$440 = eval_reg(src$438);
      ofs$442 = get_offset(ins$394);
      addr$444 = get_addr_ofs(dst64$436, ofs$442);
      step_opcode_mem_st_reg(src64$440, addr$444, pc$392, dst$400, op$396);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  int len$450;
  int pc$452;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len$450 = eval_ins_len();
    pc$452 = eval_pc();
    if (0U <= pc$452 && pc$452 < len$450) {
      step();
      f = eval_flag();
      if (f == 0) {
        upd_pc_incr();
        bpf_interpreter_aux(fuel0);
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

unsigned long long bpf_interpreter(unsigned int fuel$456)
{
  struct memory_region *mrs$458;
  struct memory_region *bpf_ctx;
  int f$462;
  mrs$458 = eval_mrs_regions();
  bpf_ctx = get_mem_region(0U, mrs$458);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(fuel$456);
  f$462 = eval_flag();
  if (f$462 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


