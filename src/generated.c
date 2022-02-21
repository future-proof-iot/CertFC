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
  if (0 == (x & 8)) {
    imm = get_immediate(ins$130);
    imm64 = eval_immediate(imm);
    return imm64;
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
  if (0 == (x$140 & 8)) {
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
  _Bool well_chunk;
  unsigned int start;
  unsigned int size;
  unsigned int mr_perm;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  well_chunk = is_well_chunk_bool(chunk$196);
  if (well_chunk) {
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
  } else {
    return 0;
  }
}

unsigned char *check_mem_aux(unsigned int num, unsigned int perm$212, unsigned int chunk$214, unsigned int addr$216, struct memory_region *mrs$218)
{
  unsigned int n$220;
  struct memory_region *cur_mr;
  unsigned char *check_mem$224;
  _Bool is_null;
  if (num == 0U) {
    return 0;
  } else {
    n$220 = num - 1U;
    cur_mr = get_mem_region(n$220, mrs$218);
    check_mem$224 = check_mem_aux2(cur_mr, perm$212, addr$216, chunk$214);
    is_null = cmp_ptr32_nullM(check_mem$224);
    if (is_null) {
      return check_mem_aux(n$220, perm$212, chunk$214, addr$216, mrs$218);
    } else {
      return check_mem$224;
    }
  }
}

unsigned char *check_mem(unsigned int perm$228, unsigned int chunk$230, unsigned int addr$232)
{
  _Bool well_chunk$234;
  unsigned int mem_reg_num;
  struct memory_region *mrs$238;
  unsigned char *check_mem$240;
  _Bool is_null$242;
  well_chunk$234 = is_well_chunk_bool(chunk$230);
  if (well_chunk$234) {
    mem_reg_num = eval_mrs_num();
    mrs$238 = eval_mrs_regions();
    check_mem$240 =
      check_mem_aux(mem_reg_num, perm$228, chunk$230, addr$232, mrs$238);
    is_null$242 = cmp_ptr32_nullM(check_mem$240);
    if (is_null$242) {
      return 0;
    } else {
      return check_mem$240;
    }
  } else {
    return 0;
  }
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64$246, unsigned int dst, unsigned char op$250)
{
  unsigned char opcode_alu64;
  unsigned int src32$254;
  unsigned int src32$256;
  unsigned int src32$258;
  opcode_alu64 = get_opcode_alu64(op$250);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64$246);
      return;
    case 16:
      upd_reg(dst, dst64 - src64$246);
      return;
    case 32:
      upd_reg(dst, dst64 * src64$246);
      return;
    case 48:
      if (src64$246 != 0LLU) {
        upd_reg(dst, dst64 / src64$246);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64$246);
      return;
    case 80:
      upd_reg(dst, dst64 & src64$246);
      return;
    case 96:
      src32$254 = reg64_to_reg32(src64$246);
      if (src32$254 < 64U) {
        upd_reg(dst, dst64 << src32$254);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32$256 = reg64_to_reg32(src64$246);
      if (src32$256 < 64U) {
        upd_reg(dst, dst64 >> src32$256);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$250 == 135) {
        upd_reg(dst, -dst64);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src64$246 != 0LLU) {
        upd_reg(dst, dst64 % src64$246);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64$246);
      return;
    case 176:
      upd_reg(dst, src64$246);
      return;
    case 192:
      src32$258 = reg64_to_reg32(src64$246);
      if (src32$258 < 64U) {
        upd_reg(dst, (unsigned long long) ((long long) dst64 >> src32$258));
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$262, unsigned int dst$264, unsigned char op$266)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$266);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$264, (unsigned long long) (dst32 + src32$262));
      return;
    case 16:
      upd_reg(dst$264, (unsigned long long) (dst32 - src32$262));
      return;
    case 32:
      upd_reg(dst$264, (unsigned long long) (dst32 * src32$262));
      return;
    case 48:
      if (src32$262 != 0U) {
        upd_reg(dst$264, (unsigned long long) (dst32 / src32$262));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$264, (unsigned long long) (dst32 | src32$262));
      return;
    case 80:
      upd_reg(dst$264, (unsigned long long) (dst32 & src32$262));
      return;
    case 96:
      if (src32$262 < 32U) {
        upd_reg(dst$264, (unsigned long long) (dst32 << src32$262));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$262 < 32U) {
        upd_reg(dst$264, (unsigned long long) (dst32 >> src32$262));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$266 == 132) {
        upd_reg(dst$264, (unsigned long long) -dst32);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src32$262 != 0U) {
        upd_reg(dst$264, (unsigned long long) (dst32 % src32$262));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$264, (unsigned long long) (dst32 ^ src32$262));
      return;
    case 176:
      upd_reg(dst$264, (unsigned long long) src32$262);
      return;
    case 192:
      if (src32$262 < 32U) {
        upd_reg(dst$264, (unsigned long long) ((int) dst32 >> src32$262));
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

void step_opcode_branch(unsigned long long dst64$270, unsigned long long src64$272, int pc, int ofs$276, unsigned char op$278)
{
  unsigned char opcode_jmp;
  unsigned char *f_ptr;
  _Bool is_null$284;
  unsigned int res;
  opcode_jmp = get_opcode_branch(op$278);
  switch (opcode_jmp) {
    case 0:
      if (op$278 == 5) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 16:
      if (dst64$270 == src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 32:
      if (dst64$270 > src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 48:
      if (dst64$270 >= src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 160:
      if (dst64$270 < src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 176:
      if (dst64$270 <= src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 64:
      if ((dst64$270 & src64$272) != 0LLU) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 80:
      if (dst64$270 != src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 96:
      if ((long long) dst64$270 > (long long) src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 112:
      if ((long long) dst64$270 >= (long long) src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 192:
      if ((long long) dst64$270 < (long long) src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 208:
      if ((long long) dst64$270 <= (long long) src64$272) {
        upd_pc(pc + ofs$276);
        return;
      } else {
        return;
      }
    case 128:
      if (op$278 == 133) {
        f_ptr = _bpf_get_call((int) src64$272);
        is_null$284 = cmp_ptr32_nullM(f_ptr);
        if (is_null$284) {
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
      if (op$278 == 149) {
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

void step_opcode_mem_ld_imm(int imm$288, int pc$290, unsigned int dst$292, unsigned char op$294)
{
  int len;
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  len = eval_ins_len();
  opcode_ld = get_opcode_mem_ld_imm(op$294);
  switch (opcode_ld) {
    case 24:
      if (pc$290 + 1 < len) {
        next_ins = eval_ins(pc$290 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$292,
                (unsigned long long) imm$288
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

void step_opcode_mem_ld_reg(unsigned int addr$304, int pc$306, unsigned int dst$308, unsigned char op$310)
{
  unsigned char opcode_ld$312;
  unsigned char *addr_ptr;
  _Bool is_null$316;
  unsigned long long v;
  unsigned char *addr_ptr$320;
  _Bool is_null$322;
  unsigned long long v$324;
  unsigned char *addr_ptr$326;
  _Bool is_null$328;
  unsigned long long v$330;
  unsigned char *addr_ptr$332;
  _Bool is_null$334;
  unsigned long long v$336;
  opcode_ld$312 = get_opcode_mem_ld_reg(op$310);
  switch (opcode_ld$312) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$304);
      is_null$316 = cmp_ptr32_nullM(addr_ptr);
      if (is_null$316) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$308, v);
        return;
      }
    case 105:
      addr_ptr$320 = check_mem(1U, 2U, addr$304);
      is_null$322 = cmp_ptr32_nullM(addr_ptr$320);
      if (is_null$322) {
        upd_flag(-2);
        return;
      } else {
        v$324 = load_mem(2U, addr_ptr$320);
        upd_reg(dst$308, v$324);
        return;
      }
    case 113:
      addr_ptr$326 = check_mem(1U, 1U, addr$304);
      is_null$328 = cmp_ptr32_nullM(addr_ptr$326);
      if (is_null$328) {
        upd_flag(-2);
        return;
      } else {
        v$330 = load_mem(1U, addr_ptr$326);
        upd_reg(dst$308, v$330);
        return;
      }
    case 121:
      addr_ptr$332 = check_mem(1U, 8U, addr$304);
      is_null$334 = cmp_ptr32_nullM(addr_ptr$332);
      if (is_null$334) {
        upd_flag(-2);
        return;
      } else {
        v$336 = load_mem(8U, addr_ptr$332);
        upd_reg(dst$308, v$336);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$338, unsigned int addr$340, int pc$342, unsigned int dst$344, unsigned char op$346)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$350;
  _Bool is_null$352;
  unsigned char *addr_ptr$354;
  _Bool is_null$356;
  unsigned char *addr_ptr$358;
  _Bool is_null$360;
  unsigned char *addr_ptr$362;
  _Bool is_null$364;
  opcode_st = get_opcode_mem_st_imm(op$346);
  switch (opcode_st) {
    case 98:
      addr_ptr$350 = check_mem(2U, 4U, addr$340);
      is_null$352 = cmp_ptr32_nullM(addr_ptr$350);
      if (is_null$352) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$350, imm$338);
        return;
      }
    case 106:
      addr_ptr$354 = check_mem(2U, 2U, addr$340);
      is_null$356 = cmp_ptr32_nullM(addr_ptr$354);
      if (is_null$356) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$354, imm$338);
        return;
      }
    case 114:
      addr_ptr$358 = check_mem(2U, 1U, addr$340);
      is_null$360 = cmp_ptr32_nullM(addr_ptr$358);
      if (is_null$360) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$358, imm$338);
        return;
      }
    case 122:
      addr_ptr$362 = check_mem(2U, 8U, addr$340);
      is_null$364 = cmp_ptr32_nullM(addr_ptr$362);
      if (is_null$364) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$362, imm$338);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$366, unsigned int addr$368, int pc$370, unsigned int dst$372, unsigned char op$374)
{
  unsigned char opcode_st$376;
  unsigned char *addr_ptr$378;
  _Bool is_null$380;
  unsigned char *addr_ptr$382;
  _Bool is_null$384;
  unsigned char *addr_ptr$386;
  _Bool is_null$388;
  unsigned char *addr_ptr$390;
  _Bool is_null$392;
  opcode_st$376 = get_opcode_mem_st_reg(op$374);
  switch (opcode_st$376) {
    case 99:
      addr_ptr$378 = check_mem(2U, 4U, addr$368);
      is_null$380 = cmp_ptr32_nullM(addr_ptr$378);
      if (is_null$380) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$378, src64$366);
        return;
      }
    case 107:
      addr_ptr$382 = check_mem(2U, 2U, addr$368);
      is_null$384 = cmp_ptr32_nullM(addr_ptr$382);
      if (is_null$384) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$382, src64$366);
        return;
      }
    case 115:
      addr_ptr$386 = check_mem(2U, 1U, addr$368);
      is_null$388 = cmp_ptr32_nullM(addr_ptr$386);
      if (is_null$388) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$386, src64$366);
        return;
      }
    case 123:
      addr_ptr$390 = check_mem(2U, 8U, addr$368);
      is_null$392 = cmp_ptr32_nullM(addr_ptr$390);
      if (is_null$392) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$390, src64$366);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  int pc$394;
  unsigned long long ins$396;
  unsigned char op$398;
  unsigned char opc;
  unsigned int dst$402;
  unsigned long long dst64$404;
  unsigned long long src64$406;
  unsigned long long dst64$408;
  unsigned int dst32$410;
  unsigned int src32$412;
  unsigned long long dst64$414;
  int ofs$416;
  unsigned long long src64$418;
  int imm$420;
  unsigned int src$422;
  unsigned long long src64$424;
  int ofs$426;
  unsigned int addr$428;
  unsigned long long dst64$430;
  int ofs$432;
  int imm$434;
  unsigned int addr$436;
  unsigned long long dst64$438;
  unsigned int src$440;
  unsigned long long src64$442;
  int ofs$444;
  unsigned int addr$446;
  pc$394 = eval_pc();
  ins$396 = eval_ins(pc$394);
  op$398 = get_opcode_ins(ins$396);
  opc = get_opcode(op$398);
  dst$402 = get_dst(ins$396);
  switch (opc) {
    case 7:
      dst64$404 = eval_reg(dst$402);
      src64$406 = get_src64(op$398, ins$396);
      step_opcode_alu64(dst64$404, src64$406, dst$402, op$398);
      return;
    case 4:
      dst64$408 = eval_reg(dst$402);
      dst32$410 = reg64_to_reg32(dst64$408);
      src32$412 = get_src32(op$398, ins$396);
      step_opcode_alu32(dst32$410, src32$412, dst$402, op$398);
      return;
    case 5:
      dst64$414 = eval_reg(dst$402);
      ofs$416 = get_offset(ins$396);
      src64$418 = get_src64(op$398, ins$396);
      step_opcode_branch(dst64$414, src64$418, pc$394, ofs$416, op$398);
      return;
    case 0:
      imm$420 = get_immediate(ins$396);
      step_opcode_mem_ld_imm(imm$420, pc$394, dst$402, op$398);
      return;
    case 1:
      src$422 = get_src(ins$396);
      src64$424 = eval_reg(src$422);
      ofs$426 = get_offset(ins$396);
      addr$428 = get_addr_ofs(src64$424, ofs$426);
      step_opcode_mem_ld_reg(addr$428, pc$394, dst$402, op$398);
      return;
    case 2:
      dst64$430 = eval_reg(dst$402);
      ofs$432 = get_offset(ins$396);
      imm$434 = get_immediate(ins$396);
      addr$436 = get_addr_ofs(dst64$430, ofs$432);
      step_opcode_mem_st_imm(imm$434, addr$436, pc$394, dst$402, op$398);
      return;
    case 3:
      dst64$438 = eval_reg(dst$402);
      src$440 = get_src(ins$396);
      src64$442 = eval_reg(src$440);
      ofs$444 = get_offset(ins$396);
      addr$446 = get_addr_ofs(dst64$438, ofs$444);
      step_opcode_mem_st_reg(src64$442, addr$446, pc$394, dst$402, op$398);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  int len$452;
  int pc$454;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len$452 = eval_ins_len();
    pc$454 = eval_pc();
    if (0U <= pc$454 && pc$454 < len$452) {
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

unsigned long long bpf_interpreter(unsigned int fuel$458)
{
  struct memory_region *mrs$460;
  struct memory_region *bpf_ctx;
  int f$464;
  mrs$460 = eval_mrs_regions();
  bpf_ctx = get_mem_region(0U, mrs$460);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(fuel$458);
  f$464 = eval_flag();
  if (f$464 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


