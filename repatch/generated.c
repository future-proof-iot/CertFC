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

extern unsigned char *get_block_ptr(struct memory_region *);

extern unsigned int get_start_addr(struct memory_region *);

extern unsigned int get_block_size(struct memory_region *);

extern unsigned int get_block_perm(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned char *check_mem_aux2(struct memory_region *, unsigned int, unsigned int, unsigned int);

extern unsigned char *check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned int, struct memory_region *);

extern unsigned char *check_mem(unsigned int, unsigned int, unsigned int);

extern _Bool comp_and_0x08_byte(unsigned char);

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

unsigned int get_src(unsigned long long ins$114)
{
  return (unsigned int) ((ins$114 & 65535LLU) >> 12LLU);
}

int get_offset(unsigned long long ins$116)
{
  return (int) (short) (ins$116 << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins$118)
{
  return (int) (ins$118 >> 32LLU);
}

long long eval_immediate(int ins$120)
{
  return (long long) ins$120;
}

unsigned char get_opcode_ins(unsigned long long ins$122)
{
  return (unsigned char) (ins$122 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$126)
{
  return (unsigned char) (op$126 & 240);
}

unsigned char get_opcode_branch(unsigned char op$128)
{
  return (unsigned char) (op$128 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$130)
{
  return (unsigned char) (op$130 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$132)
{
  return (unsigned char) (op$132 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$134)
{
  return (unsigned char) (op$134 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$136)
{
  return (unsigned char) (op$136 & 255);
}

unsigned char get_opcode(unsigned char op$138)
{
  return (unsigned char) (op$138 & 7);
}

unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}

unsigned int get_sub(unsigned int x$144, unsigned int y$146)
{
  return x$144 - y$146;
}

unsigned int get_addr_ofs(unsigned long long x$148, int ofs)
{
  return (unsigned int) (x$148 + (unsigned long long) ofs);
}

unsigned char *get_block_ptr(struct memory_region *mr)
{
  return (*mr).block_ptr;
}

unsigned int get_start_addr(struct memory_region *mr$154)
{
  return (*mr$154).start_addr;
}

unsigned int get_block_size(struct memory_region *mr$156)
{
  return (*mr$156).block_size;
}

unsigned int get_block_perm(struct memory_region *mr$158)
{
  return (*mr$158).block_perm;
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

unsigned char *check_mem_aux2(struct memory_region *mr$162, unsigned int perm, unsigned int addr, unsigned int chunk$168)
{
  _Bool well_chunk;
  unsigned char *ptr;
  unsigned int start;
  unsigned int size;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  unsigned int mr_perm;
  well_chunk = is_well_chunk_bool(chunk$168);
  if (well_chunk) {
    ptr = get_block_ptr(mr$162);
    start = get_start_addr(mr$162);
    size = get_block_size(mr$162);
    lo_ofs = get_sub(addr, start);
    hi_ofs = get_add(lo_ofs, chunk$168);
    if (0U <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 4294967295U - chunk$168 && 0U == lo_ofs % chunk$168) {
        mr_perm = get_block_perm(mr$162);
        if (mr_perm >= perm) {
          return ptr + lo_ofs;
        } else {
          return 0;
        }
      } else {
        return 0;
      }
    } else {
      return 0;
    }
  } else {
    return 0;
  }
}

unsigned char *check_mem_aux(unsigned int num, unsigned int perm$186, unsigned int chunk$188, unsigned int addr$190, struct memory_region *mrs$192)
{
  unsigned int n$194;
  struct memory_region *cur_mr;
  unsigned char *check_mem$198;
  if (num == 0U) {
    return 0;
  } else {
    n$194 = num - 1U;
    cur_mr = get_mem_region(n$194, mrs$192);
    check_mem$198 = check_mem_aux2(cur_mr, perm$186, addr$190, chunk$188);
    if (check_mem$198 == 0) {
      return check_mem_aux(n$194, perm$186, chunk$188, addr$190, mrs$192);
    } else {
      return check_mem$198;
    }
  }
}

unsigned char *check_mem(unsigned int perm$200, unsigned int chunk$202, unsigned int addr$204)
{
  _Bool well_chunk$206;
  unsigned int mem_reg_num;
  struct memory_region *mrs$210;
  unsigned char *check_mem$212;
  well_chunk$206 = is_well_chunk_bool(chunk$202);
  if (well_chunk$206) {
    mem_reg_num = eval_mrs_num();
    mrs$210 = eval_mrs_regions();
    check_mem$212 =
      check_mem_aux(mem_reg_num, perm$200, chunk$202, addr$204, mrs$210);
    if (check_mem$212 == 0) {
      return 0;
    } else {
      return check_mem$212;
    }
  } else {
    return 0;
  }
}

_Bool comp_and_0x08_byte(unsigned char x$214)
{
  return 0 == (x$214 & 8);
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64, unsigned int dst, unsigned char op$222)
{
  unsigned char opcode_alu64;
  unsigned int src32;
  unsigned int src32$228;
  unsigned int src32$230;
  opcode_alu64 = get_opcode_alu64(op$222);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64);
      return;
    case 16:
      upd_reg(dst, dst64 - src64);
      return;
    case 32:
      upd_reg(dst, dst64 * src64);
      return;
    case 48:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 / src64);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64);
      return;
    case 80:
      upd_reg(dst, dst64 & src64);
      return;
    case 96:
      src32 = reg64_to_reg32(src64);
      if (src32 < 64U) {
        upd_reg(dst, dst64 << src32);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32$228 = reg64_to_reg32(src64);
      if (src32$228 < 64U) {
        upd_reg(dst, dst64 >> src32$228);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$222 == 135) {
        upd_reg(dst, -dst64);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % src64);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64);
      return;
    case 176:
      upd_reg(dst, src64);
      return;
    case 192:
      src32$230 = reg64_to_reg32(src64);
      if (src32$230 < 64U) {
        upd_reg(dst, (long long) dst64 >> src32$230);
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$234, unsigned int dst$236, unsigned char op$238)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$238);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$236, (unsigned long long) (dst32 + src32$234));
      return;
    case 16:
      upd_reg(dst$236, (unsigned long long) (dst32 - src32$234));
      return;
    case 32:
      upd_reg(dst$236, (unsigned long long) (dst32 * src32$234));
      return;
    case 48:
      if (src32$234 != 0U) {
        upd_reg(dst$236, (unsigned long long) (dst32 / src32$234));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$236, (unsigned long long) (dst32 | src32$234));
      return;
    case 80:
      upd_reg(dst$236, (unsigned long long) (dst32 & src32$234));
      return;
    case 96:
      if (src32$234 < 32U) {
        upd_reg(dst$236, (unsigned long long) (dst32 << src32$234));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$234 < 32U) {
        upd_reg(dst$236, (unsigned long long) (dst32 >> src32$234));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$238 == 132) {
        upd_reg(dst$236, (unsigned long long) -dst32);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src32$234 != 0U) {
        upd_reg(dst$236, (unsigned long long) (dst32 % src32$234));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$236, (unsigned long long) (dst32 ^ src32$234));
      return;
    case 176:
      upd_reg(dst$236, (unsigned long long) src32$234);
      return;
    case 192:
      if (src32$234 < 32U) {
        upd_reg(dst$236, (unsigned long long) ((int) dst32 >> src32$234));
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

void step_opcode_branch(unsigned long long dst64$242, unsigned long long src64$244, int pc, int ofs$248, unsigned char op$250)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op$250);
  switch (opcode_jmp) {
    case 0:
      if (op$250 == 5) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 16:
      if (dst64$242 == src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 32:
      if (dst64$242 > src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 48:
      if (dst64$242 >= src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 160:
      if (dst64$242 < src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 176:
      if (dst64$242 <= src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 64:
      if ((dst64$242 & src64$244) != 0LLU) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 80:
      if (dst64$242 != src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 96:
      if ((long long) dst64$242 > (long long) src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 112:
      if ((long long) dst64$242 >= (long long) src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 192:
      if ((long long) dst64$242 < (long long) src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 208:
      if ((long long) dst64$242 <= (long long) src64$244) {
        upd_pc(pc + ofs$248);
        return;
      } else {
        return;
      }
    case 144:
      if (op$250 == 149) {
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

void step_opcode_mem_ld_imm(int imm, int pc$256, unsigned int dst$258, unsigned char op$260)
{
  int len;
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  len = eval_ins_len();
  opcode_ld = get_opcode_mem_ld_imm(op$260);
  switch (opcode_ld) {
    case 24:
      if (pc$256 + 1 < len) {
        next_ins = eval_ins(pc$256 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$258,
                (unsigned long long) imm
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

void step_opcode_mem_ld_reg(unsigned int addr$270, int pc$272, unsigned int dst$274, unsigned char op$276)
{
  unsigned char opcode_ld$278;
  unsigned char *addr_ptr;
  unsigned long long v;
  unsigned char *addr_ptr$284;
  unsigned long long v$286;
  unsigned char *addr_ptr$288;
  unsigned long long v$290;
  unsigned char *addr_ptr$292;
  unsigned long long v$294;
  opcode_ld$278 = get_opcode_mem_ld_reg(op$276);
  switch (opcode_ld$278) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$270);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$274, v);
        return;
      }
    case 105:
      addr_ptr$284 = check_mem(1U, 2U, addr$270);
      if (addr_ptr$284 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$286 = load_mem(2U, addr_ptr$284);
        upd_reg(dst$274, v$286);
        return;
      }
    case 113:
      addr_ptr$288 = check_mem(1U, 1U, addr$270);
      if (addr_ptr$288 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$290 = load_mem(1U, addr_ptr$288);
        upd_reg(dst$274, v$290);
        return;
      }
    case 121:
      addr_ptr$292 = check_mem(1U, 8U, addr$270);
      if (addr_ptr$292 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$294 = load_mem(8U, addr_ptr$292);
        upd_reg(dst$274, v$294);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$296, unsigned int addr$298, int pc$300, unsigned int dst$302, unsigned char op$304)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$308;
  unsigned char *addr_ptr$310;
  unsigned char *addr_ptr$312;
  unsigned char *addr_ptr$314;
  opcode_st = get_opcode_mem_st_imm(op$304);
  switch (opcode_st) {
    case 98:
      addr_ptr$308 = check_mem(2U, 4U, addr$298);
      if (addr_ptr$308 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$308, imm$296);
        return;
      }
    case 106:
      addr_ptr$310 = check_mem(2U, 2U, addr$298);
      if (addr_ptr$310 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$310, imm$296);
        return;
      }
    case 114:
      addr_ptr$312 = check_mem(2U, 1U, addr$298);
      if (addr_ptr$312 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$312, imm$296);
        return;
      }
    case 122:
      addr_ptr$314 = check_mem(2U, 8U, addr$298);
      if (addr_ptr$314 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$314, imm$296);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$316, unsigned int addr$318, int pc$320, unsigned int dst$322, unsigned char op$324)
{
  unsigned char opcode_st$326;
  unsigned char *addr_ptr$328;
  unsigned char *addr_ptr$330;
  unsigned char *addr_ptr$332;
  unsigned char *addr_ptr$334;
  opcode_st$326 = get_opcode_mem_st_reg(op$324);
  switch (opcode_st$326) {
    case 99:
      addr_ptr$328 = check_mem(2U, 4U, addr$318);
      if (addr_ptr$328 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$328, src64$316);
        return;
      }
    case 107:
      addr_ptr$330 = check_mem(2U, 2U, addr$318);
      if (addr_ptr$330 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$330, src64$316);
        return;
      }
    case 115:
      addr_ptr$332 = check_mem(2U, 1U, addr$318);
      if (addr_ptr$332 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$332, src64$316);
        return;
      }
    case 123:
      addr_ptr$334 = check_mem(2U, 8U, addr$318);
      if (addr_ptr$334 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$334, src64$316);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  int pc$336;
  unsigned long long ins$338;
  unsigned char op$340;
  unsigned char opc;
  unsigned int dst$344;
  unsigned long long dst64$346;
  _Bool is_imm;
  int imm$350;
  long long imm64;
  unsigned int src;
  unsigned long long src64$356;
  unsigned int dst$358;
  unsigned long long dst64$360;
  unsigned int dst32$362;
  _Bool is_imm$364;
  int imm$366;
  unsigned int src$368;
  unsigned long long src64$370;
  unsigned int src32$372;
  unsigned int dst$374;
  unsigned long long dst64$376;
  int ofs$378;
  _Bool is_imm$380;
  int imm$382;
  long long imm64$384;
  unsigned int src$386;
  unsigned long long src64$388;
  unsigned int dst$390;
  int imm$392;
  unsigned int dst$394;
  unsigned int src$396;
  unsigned long long src64$398;
  int ofs$400;
  unsigned int addr$402;
  unsigned int dst$404;
  unsigned long long dst64$406;
  int ofs$408;
  int imm$410;
  unsigned int addr$412;
  unsigned int dst$414;
  unsigned long long dst64$416;
  unsigned int src$418;
  unsigned long long src64$420;
  int ofs$422;
  unsigned int addr$424;
  pc$336 = eval_pc();
  ins$338 = eval_ins(pc$336);
  op$340 = get_opcode_ins(ins$338);
  opc = get_opcode(op$340);
  switch (opc) {
    case 7:
      dst$344 = get_dst(ins$338);
      dst64$346 = eval_reg(dst$344);
      is_imm = comp_and_0x08_byte(op$340);
      if (is_imm) {
        imm$350 = get_immediate(ins$338);
        imm64 = eval_immediate(imm$350);
        step_opcode_alu64(dst64$346, imm64, dst$344, op$340);
        return;
      } else {
        src = get_src(ins$338);
        src64$356 = eval_reg(src);
        step_opcode_alu64(dst64$346, src64$356, dst$344, op$340);
        return;
      }
    case 4:
      dst$358 = get_dst(ins$338);
      dst64$360 = eval_reg(dst$358);
      dst32$362 = reg64_to_reg32(dst64$360);
      is_imm$364 = comp_and_0x08_byte(op$340);
      if (is_imm$364) {
        imm$366 = get_immediate(ins$338);
        step_opcode_alu32(dst32$362, imm$366, dst$358, op$340);
        return;
      } else {
        src$368 = get_src(ins$338);
        src64$370 = eval_reg(src$368);
        src32$372 = reg64_to_reg32(src64$370);
        step_opcode_alu32(dst32$362, src32$372, dst$358, op$340);
        return;
      }
    case 5:
      dst$374 = get_dst(ins$338);
      dst64$376 = eval_reg(dst$374);
      ofs$378 = get_offset(ins$338);
      is_imm$380 = comp_and_0x08_byte(op$340);
      if (is_imm$380) {
        imm$382 = get_immediate(ins$338);
        imm64$384 = eval_immediate(imm$382);
        step_opcode_branch(dst64$376, imm64$384, pc$336, ofs$378, op$340);
        return;
      } else {
        src$386 = get_src(ins$338);
        src64$388 = eval_reg(src$386);
        step_opcode_branch(dst64$376, src64$388, pc$336, ofs$378, op$340);
        return;
      }
    case 0:
      dst$390 = get_dst(ins$338);
      imm$392 = get_immediate(ins$338);
      step_opcode_mem_ld_imm(imm$392, pc$336, dst$390, op$340);
      return;
    case 1:
      dst$394 = get_dst(ins$338);
      src$396 = get_src(ins$338);
      src64$398 = eval_reg(src$396);
      ofs$400 = get_offset(ins$338);
      addr$402 = get_addr_ofs(src64$398, ofs$400);
      step_opcode_mem_ld_reg(addr$402, pc$336, dst$394, op$340);
      return;
    case 2:
      dst$404 = get_dst(ins$338);
      dst64$406 = eval_reg(dst$404);
      ofs$408 = get_offset(ins$338);
      imm$410 = get_immediate(ins$338);
      addr$412 = get_addr_ofs(dst64$406, ofs$408);
      step_opcode_mem_st_imm(imm$410, addr$412, pc$336, dst$404, op$340);
      return;
    case 3:
      dst$414 = get_dst(ins$338);
      dst64$416 = eval_reg(dst$414);
      src$418 = get_src(ins$338);
      src64$420 = eval_reg(src$418);
      ofs$422 = get_offset(ins$338);
      addr$424 = get_addr_ofs(dst64$416, ofs$422);
      step_opcode_mem_st_reg(src64$420, addr$424, pc$336, dst$414, op$340);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  int len$430;
  int pc$432;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len$430 = eval_ins_len();
    pc$432 = eval_pc();
    if (0U <= pc$432 && pc$432 < len$430) {
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

unsigned long long bpf_interpreter(unsigned int fuel$436)
{
  struct memory_region *mrs$438;
  struct memory_region *bpf_ctx;
  int f$442;
  mrs$438 = eval_mrs_regions();
  bpf_ctx = get_mem_region(0U, mrs$438);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(fuel$436);
  f$442 = eval_flag();
  if (f$442 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


