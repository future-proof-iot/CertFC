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

unsigned int get_src(unsigned long long ins$116)
{
  return (unsigned int) ((ins$116 & 65535LLU) >> 12LLU);
}

int get_offset(unsigned long long ins$118)
{
  return (int) (short) (ins$118 << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins$120)
{
  return (int) (ins$120 >> 32LLU);
}

long long eval_immediate(int ins$122)
{
  return (long long) ins$122;
}

unsigned long long get_src64(unsigned char x, unsigned long long ins$126)
{
  int imm;
  long long imm64;
  unsigned int src;
  unsigned long long src64;
  if (0 == (x & 8)) {
    imm = get_immediate(ins$126);
    imm64 = eval_immediate(imm);
    return imm64;
  } else {
    src = get_src(ins$126);
    src64 = eval_reg(src);
    return src64;
  }
}

unsigned int get_src32(unsigned char x$136, unsigned long long ins$138)
{
  int imm$140;
  unsigned int src$142;
  unsigned long long src64$144;
  unsigned int src32;
  if (0 == (x$136 & 8)) {
    imm$140 = get_immediate(ins$138);
    return imm$140;
  } else {
    src$142 = get_src(ins$138);
    src64$144 = eval_reg(src$142);
    src32 = reg64_to_reg32(src64$144);
    return src32;
  }
}

unsigned char get_opcode_ins(unsigned long long ins$148)
{
  return (unsigned char) (ins$148 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$152)
{
  return (unsigned char) (op$152 & 240);
}

unsigned char get_opcode_branch(unsigned char op$154)
{
  return (unsigned char) (op$154 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$156)
{
  return (unsigned char) (op$156 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$158)
{
  return (unsigned char) (op$158 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$160)
{
  return (unsigned char) (op$160 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$162)
{
  return (unsigned char) (op$162 & 255);
}

unsigned char get_opcode(unsigned char op$164)
{
  return (unsigned char) (op$164 & 7);
}

unsigned int get_add(unsigned int x$166, unsigned int y)
{
  return x$166 + y;
}

unsigned int get_sub(unsigned int x$170, unsigned int y$172)
{
  return x$170 - y$172;
}

unsigned int get_addr_ofs(unsigned long long x$174, int ofs)
{
  return (unsigned int) (x$174 + (unsigned long long) ofs);
}

unsigned int get_start_addr(struct memory_region *mr)
{
  return (*mr).start_addr;
}

unsigned int get_block_size(struct memory_region *mr$180)
{
  return (*mr$180).block_size;
}

unsigned int get_block_perm(struct memory_region *mr$182)
{
  return (*mr$182).block_perm;
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

unsigned char *check_mem_aux2(struct memory_region *mr$186, unsigned int perm, unsigned int addr, unsigned int chunk$192)
{
  _Bool well_chunk;
  unsigned int start;
  unsigned int size;
  unsigned int mr_perm;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  well_chunk = is_well_chunk_bool(chunk$192);
  if (well_chunk) {
    start = get_start_addr(mr$186);
    size = get_block_size(mr$186);
    mr_perm = get_block_perm(mr$186);
    lo_ofs = get_sub(addr, start);
    hi_ofs = get_add(lo_ofs, chunk$192);
    if (hi_ofs < size
          && (lo_ofs <= 4294967295U - chunk$192 && 0U == lo_ofs % chunk$192)
          && mr_perm >= perm) {
      return (*mr$186).block_ptr + lo_ofs;
    } else {
      return 0;
    }
  } else {
    return 0;
  }
}

unsigned char *check_mem_aux(unsigned int num, unsigned int perm$208, unsigned int chunk$210, unsigned int addr$212, struct memory_region *mrs$214)
{
  unsigned int n$216;
  struct memory_region *cur_mr;
  unsigned char *check_mem$220;
  _Bool is_null;
  if (num == 0U) {
    return 0;
  } else {
    n$216 = num - 1U;
    cur_mr = get_mem_region(n$216, mrs$214);
    check_mem$220 = check_mem_aux2(cur_mr, perm$208, addr$212, chunk$210);
    is_null = cmp_ptr32_nullM(check_mem$220);
    if (is_null) {
      return check_mem_aux(n$216, perm$208, chunk$210, addr$212, mrs$214);
    } else {
      return check_mem$220;
    }
  }
}

unsigned char *check_mem(unsigned int perm$224, unsigned int chunk$226, unsigned int addr$228)
{
  _Bool well_chunk$230;
  unsigned int mem_reg_num;
  struct memory_region *mrs$234;
  unsigned char *check_mem$236;
  _Bool is_null$238;
  well_chunk$230 = is_well_chunk_bool(chunk$226);
  if (well_chunk$230) {
    mem_reg_num = eval_mrs_num();
    mrs$234 = eval_mrs_regions();
    check_mem$236 =
      check_mem_aux(mem_reg_num, perm$224, chunk$226, addr$228, mrs$234);
    is_null$238 = cmp_ptr32_nullM(check_mem$236);
    if (is_null$238) {
      return 0;
    } else {
      return check_mem$236;
    }
  } else {
    return 0;
  }
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64$242, unsigned int dst, unsigned char op$246)
{
  unsigned char opcode_alu64;
  unsigned int src32$250;
  unsigned int src32$252;
  unsigned int src32$254;
  opcode_alu64 = get_opcode_alu64(op$246);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64$242);
      return;
    case 16:
      upd_reg(dst, dst64 - src64$242);
      return;
    case 32:
      upd_reg(dst, dst64 * src64$242);
      return;
    case 48:
      if (src64$242 != 0LLU) {
        upd_reg(dst, dst64 / src64$242);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64$242);
      return;
    case 80:
      upd_reg(dst, dst64 & src64$242);
      return;
    case 96:
      src32$250 = reg64_to_reg32(src64$242);
      if (src32$250 < 64U) {
        upd_reg(dst, dst64 << src32$250);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32$252 = reg64_to_reg32(src64$242);
      if (src32$252 < 64U) {
        upd_reg(dst, dst64 >> src32$252);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$246 == 135) {
        upd_reg(dst, -dst64);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src64$242 != 0LLU) {
        upd_reg(dst, dst64 % src64$242);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64$242);
      return;
    case 176:
      upd_reg(dst, src64$242);
      return;
    case 192:
      src32$254 = reg64_to_reg32(src64$242);
      if (src32$254 < 64U) {
        upd_reg(dst, (unsigned long long) ((long long) dst64 >> src32$254));
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$258, unsigned int dst$260, unsigned char op$262)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$262);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$260, (unsigned long long) (dst32 + src32$258));
      return;
    case 16:
      upd_reg(dst$260, (unsigned long long) (dst32 - src32$258));
      return;
    case 32:
      upd_reg(dst$260, (unsigned long long) (dst32 * src32$258));
      return;
    case 48:
      if (src32$258 != 0U) {
        upd_reg(dst$260, (unsigned long long) (dst32 / src32$258));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$260, (unsigned long long) (dst32 | src32$258));
      return;
    case 80:
      upd_reg(dst$260, (unsigned long long) (dst32 & src32$258));
      return;
    case 96:
      if (src32$258 < 32U) {
        upd_reg(dst$260, (unsigned long long) (dst32 << src32$258));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$258 < 32U) {
        upd_reg(dst$260, (unsigned long long) (dst32 >> src32$258));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$262 == 132) {
        upd_reg(dst$260, (unsigned long long) -dst32);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src32$258 != 0U) {
        upd_reg(dst$260, (unsigned long long) (dst32 % src32$258));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$260, (unsigned long long) (dst32 ^ src32$258));
      return;
    case 176:
      upd_reg(dst$260, (unsigned long long) src32$258);
      return;
    case 192:
      if (src32$258 < 32U) {
        upd_reg(dst$260, (unsigned long long) ((int) dst32 >> src32$258));
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

void step_opcode_branch(unsigned long long dst64$266, unsigned long long src64$268, int pc, int ofs$272, unsigned char op$274)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op$274);
  switch (opcode_jmp) {
    case 0:
      if (op$274 == 5) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 16:
      if (dst64$266 == src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 32:
      if (dst64$266 > src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 48:
      if (dst64$266 >= src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 160:
      if (dst64$266 < src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 176:
      if (dst64$266 <= src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 64:
      if ((dst64$266 & src64$268) != 0LLU) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 80:
      if (dst64$266 != src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 96:
      if ((long long) dst64$266 > (long long) src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 112:
      if ((long long) dst64$266 >= (long long) src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 192:
      if ((long long) dst64$266 < (long long) src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 208:
      if ((long long) dst64$266 <= (long long) src64$268) {
        upd_pc(pc + ofs$272);
        return;
      } else {
        return;
      }
    case 144:
      if (op$274 == 149) {
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

void step_opcode_mem_ld_imm(int imm$278, int pc$280, unsigned int dst$282, unsigned char op$284)
{
  int len;
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  len = eval_ins_len();
  opcode_ld = get_opcode_mem_ld_imm(op$284);
  switch (opcode_ld) {
    case 24:
      if (pc$280 + 1 < len) {
        next_ins = eval_ins(pc$280 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$282,
                (unsigned long long) imm$278
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

void step_opcode_mem_ld_reg(unsigned int addr$294, int pc$296, unsigned int dst$298, unsigned char op$300)
{
  unsigned char opcode_ld$302;
  unsigned char *addr_ptr;
  _Bool is_null$306;
  unsigned long long v;
  unsigned char *addr_ptr$310;
  _Bool is_null$312;
  unsigned long long v$314;
  unsigned char *addr_ptr$316;
  _Bool is_null$318;
  unsigned long long v$320;
  unsigned char *addr_ptr$322;
  _Bool is_null$324;
  unsigned long long v$326;
  opcode_ld$302 = get_opcode_mem_ld_reg(op$300);
  switch (opcode_ld$302) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$294);
      is_null$306 = cmp_ptr32_nullM(addr_ptr);
      if (is_null$306) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$298, v);
        return;
      }
    case 105:
      addr_ptr$310 = check_mem(1U, 2U, addr$294);
      is_null$312 = cmp_ptr32_nullM(addr_ptr$310);
      if (is_null$312) {
        upd_flag(-2);
        return;
      } else {
        v$314 = load_mem(2U, addr_ptr$310);
        upd_reg(dst$298, v$314);
        return;
      }
    case 113:
      addr_ptr$316 = check_mem(1U, 1U, addr$294);
      is_null$318 = cmp_ptr32_nullM(addr_ptr$316);
      if (is_null$318) {
        upd_flag(-2);
        return;
      } else {
        v$320 = load_mem(1U, addr_ptr$316);
        upd_reg(dst$298, v$320);
        return;
      }
    case 121:
      addr_ptr$322 = check_mem(1U, 8U, addr$294);
      is_null$324 = cmp_ptr32_nullM(addr_ptr$322);
      if (is_null$324) {
        upd_flag(-2);
        return;
      } else {
        v$326 = load_mem(8U, addr_ptr$322);
        upd_reg(dst$298, v$326);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$328, unsigned int addr$330, int pc$332, unsigned int dst$334, unsigned char op$336)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$340;
  _Bool is_null$342;
  unsigned char *addr_ptr$344;
  _Bool is_null$346;
  unsigned char *addr_ptr$348;
  _Bool is_null$350;
  unsigned char *addr_ptr$352;
  _Bool is_null$354;
  opcode_st = get_opcode_mem_st_imm(op$336);
  switch (opcode_st) {
    case 98:
      addr_ptr$340 = check_mem(2U, 4U, addr$330);
      is_null$342 = cmp_ptr32_nullM(addr_ptr$340);
      if (is_null$342) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$340, imm$328);
        return;
      }
    case 106:
      addr_ptr$344 = check_mem(2U, 2U, addr$330);
      is_null$346 = cmp_ptr32_nullM(addr_ptr$344);
      if (is_null$346) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$344, imm$328);
        return;
      }
    case 114:
      addr_ptr$348 = check_mem(2U, 1U, addr$330);
      is_null$350 = cmp_ptr32_nullM(addr_ptr$348);
      if (is_null$350) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$348, imm$328);
        return;
      }
    case 122:
      addr_ptr$352 = check_mem(2U, 8U, addr$330);
      is_null$354 = cmp_ptr32_nullM(addr_ptr$352);
      if (is_null$354) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$352, imm$328);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$356, unsigned int addr$358, int pc$360, unsigned int dst$362, unsigned char op$364)
{
  unsigned char opcode_st$366;
  unsigned char *addr_ptr$368;
  _Bool is_null$370;
  unsigned char *addr_ptr$372;
  _Bool is_null$374;
  unsigned char *addr_ptr$376;
  _Bool is_null$378;
  unsigned char *addr_ptr$380;
  _Bool is_null$382;
  opcode_st$366 = get_opcode_mem_st_reg(op$364);
  switch (opcode_st$366) {
    case 99:
      addr_ptr$368 = check_mem(2U, 4U, addr$358);
      is_null$370 = cmp_ptr32_nullM(addr_ptr$368);
      if (is_null$370) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$368, src64$356);
        return;
      }
    case 107:
      addr_ptr$372 = check_mem(2U, 2U, addr$358);
      is_null$374 = cmp_ptr32_nullM(addr_ptr$372);
      if (is_null$374) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$372, src64$356);
        return;
      }
    case 115:
      addr_ptr$376 = check_mem(2U, 1U, addr$358);
      is_null$378 = cmp_ptr32_nullM(addr_ptr$376);
      if (is_null$378) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$376, src64$356);
        return;
      }
    case 123:
      addr_ptr$380 = check_mem(2U, 8U, addr$358);
      is_null$382 = cmp_ptr32_nullM(addr_ptr$380);
      if (is_null$382) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$380, src64$356);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  int pc$384;
  unsigned long long ins$386;
  unsigned char op$388;
  unsigned char opc;
  unsigned int dst$392;
  unsigned long long dst64$394;
  unsigned long long src64$396;
  unsigned long long dst64$398;
  unsigned int dst32$400;
  unsigned int src32$402;
  unsigned long long dst64$404;
  int ofs$406;
  unsigned long long src64$408;
  int imm$410;
  unsigned int src$412;
  unsigned long long src64$414;
  int ofs$416;
  unsigned int addr$418;
  unsigned long long dst64$420;
  int ofs$422;
  int imm$424;
  unsigned int addr$426;
  unsigned long long dst64$428;
  unsigned int src$430;
  unsigned long long src64$432;
  int ofs$434;
  unsigned int addr$436;
  pc$384 = eval_pc();
  ins$386 = eval_ins(pc$384);
  op$388 = get_opcode_ins(ins$386);
  opc = get_opcode(op$388);
  dst$392 = get_dst(ins$386);
  switch (opc) {
    case 7:
      dst64$394 = eval_reg(dst$392);
      src64$396 = get_src64(op$388, ins$386);
      step_opcode_alu64(dst64$394, src64$396, dst$392, op$388);
      return;
    case 4:
      dst64$398 = eval_reg(dst$392);
      dst32$400 = reg64_to_reg32(dst64$398);
      src32$402 = get_src32(op$388, ins$386);
      step_opcode_alu32(dst32$400, src32$402, dst$392, op$388);
      return;
    case 5:
      dst64$404 = eval_reg(dst$392);
      ofs$406 = get_offset(ins$386);
      src64$408 = get_src64(op$388, ins$386);
      step_opcode_branch(dst64$404, src64$408, pc$384, ofs$406, op$388);
      return;
    case 0:
      imm$410 = get_immediate(ins$386);
      step_opcode_mem_ld_imm(imm$410, pc$384, dst$392, op$388);
      return;
    case 1:
      src$412 = get_src(ins$386);
      src64$414 = eval_reg(src$412);
      ofs$416 = get_offset(ins$386);
      addr$418 = get_addr_ofs(src64$414, ofs$416);
      step_opcode_mem_ld_reg(addr$418, pc$384, dst$392, op$388);
      return;
    case 2:
      dst64$420 = eval_reg(dst$392);
      ofs$422 = get_offset(ins$386);
      imm$424 = get_immediate(ins$386);
      addr$426 = get_addr_ofs(dst64$420, ofs$422);
      step_opcode_mem_st_imm(imm$424, addr$426, pc$384, dst$392, op$388);
      return;
    case 3:
      dst64$428 = eval_reg(dst$392);
      src$430 = get_src(ins$386);
      src64$432 = eval_reg(src$430);
      ofs$434 = get_offset(ins$386);
      addr$436 = get_addr_ofs(dst64$428, ofs$434);
      step_opcode_mem_st_reg(src64$432, addr$436, pc$384, dst$392, op$388);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  int len$442;
  int pc$444;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len$442 = eval_ins_len();
    pc$444 = eval_pc();
    if (0U <= pc$444 && pc$444 < len$442) {
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

unsigned long long bpf_interpreter(unsigned int fuel$448)
{
  struct memory_region *mrs$450;
  struct memory_region *bpf_ctx;
  int f$454;
  mrs$450 = eval_mrs_regions();
  bpf_ctx = get_mem_region(0U, mrs$450);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(fuel$448);
  f$454 = eval_flag();
  if (f$454 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


