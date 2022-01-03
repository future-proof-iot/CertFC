struct memory_region;
struct bpf_state;
struct memory_region {
  unsigned int *start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned int *block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned long long regsmap[11];
  struct memory_region *mrs$757165;
  unsigned int mrs_num;
};

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

extern unsigned int get_add(unsigned int, unsigned int);

extern unsigned int get_sub(unsigned int, unsigned int);

extern unsigned int get_addr_ofs(unsigned long long, int);

extern unsigned int *get_block_ptr(struct memory_region *);

extern unsigned int get_start_addr(struct memory_region *);

extern unsigned int get_block_size(struct memory_region *);

extern unsigned int get_block_perm(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned int *check_mem_aux2(struct memory_region *, unsigned int, unsigned int);

extern unsigned int *check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned int);

extern unsigned int *check_mem(unsigned int, unsigned int, unsigned int);

extern _Bool comp_and_0x08_byte(unsigned char);

extern void step_opcode_alu64(unsigned long long, unsigned long long, unsigned int, unsigned char);

extern void step_opcode_alu32(unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_branch(unsigned long long, unsigned long long, int, int, unsigned char);

extern void step_opcode_mem_ld_imm(int, int, int, unsigned int, unsigned char, unsigned long long *);

extern void step_opcode_mem_ld_reg(unsigned int, int, unsigned int, unsigned char);

extern void step_opcode_mem_st_imm(int, unsigned int, int, unsigned int, unsigned char);

extern void step_opcode_mem_st_reg(unsigned long long, unsigned int, int, unsigned int, unsigned char);

extern void step(int, unsigned long long *);

extern void bpf_interpreter_aux(int, unsigned int, unsigned long long *);

extern unsigned long long bpf_interpreter(int, unsigned int, unsigned long long *);

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

unsigned long long list_get(unsigned long long *l, int idx)
{
  return *(l + idx);
}

struct memory_region *get_mem_region(unsigned int n)
{
  struct memory_region *mrs;
  mrs = eval_mrs_regions();
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

unsigned long long eval_immediate(int ins$122)
{
  return (unsigned long long) (unsigned int) ins$122;
}

unsigned char get_opcode_ins(unsigned long long ins$124)
{
  return (unsigned char) (ins$124 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$128)
{
  return (unsigned char) (op$128 & 240);
}

unsigned char get_opcode_branch(unsigned char op$130)
{
  return (unsigned char) (op$130 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$132)
{
  return (unsigned char) (op$132 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$134)
{
  return (unsigned char) (op$134 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$136)
{
  return (unsigned char) (op$136 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$138)
{
  return (unsigned char) (op$138 & 255);
}

unsigned char get_opcode(unsigned char op$140)
{
  return (unsigned char) (op$140 & 7);
}

unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}

unsigned int get_sub(unsigned int x$146, unsigned int y$148)
{
  return x$146 - y$148;
}

unsigned int get_addr_ofs(unsigned long long x$150, int ofs)
{
  return (unsigned int) (x$150 + (unsigned long long) ofs);
}

unsigned int *get_block_ptr(struct memory_region *mr)
{
  return (*mr).block_ptr;
}

unsigned int get_start_addr(struct memory_region *mr$156)
{
  return (*mr$156).start_addr;
}

unsigned int get_block_size(struct memory_region *mr$158)
{
  return (*mr$158).block_size;
}

unsigned int get_block_perm(struct memory_region *mr$160)
{
  return (*mr$160).block_perm;
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

unsigned int *check_mem_aux2(struct memory_region *mr$164, unsigned int addr, unsigned int chunk$168)
{
  _Bool well_chunk;
  unsigned int *ptr;
  unsigned int start;
  unsigned int size;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  well_chunk = is_well_chunk_bool(chunk$168);
  if (well_chunk) {
    ptr = get_block_ptr(mr$164);
    start = get_start_addr(mr$164);
    size = get_block_size(mr$164);
    lo_ofs = get_sub(addr, start);
    hi_ofs = get_add(lo_ofs, chunk$168);
    if (0U <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 4294967295U - chunk$168 && 0U == lo_ofs % chunk$168) {
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
}

unsigned int *check_mem_aux(unsigned int num, unsigned int perm, unsigned int chunk$186, unsigned int addr$188)
{
  unsigned int n$190;
  struct memory_region *cur_mr;
  unsigned int mr_perm;
  unsigned int *check_mem$196;
  if (num == 0U) {
    return 0;
  } else {
    n$190 = num - 1U;
    cur_mr = get_mem_region(n$190);
    mr_perm = get_block_perm(cur_mr);
    if (mr_perm >= perm) {
      check_mem$196 = check_mem_aux2(cur_mr, addr$188, chunk$186);
      if (check_mem$196 == 0) {
        return check_mem_aux(n$190, perm, chunk$186, addr$188);
      } else {
        return check_mem$196;
      }
    } else {
      return check_mem_aux(n$190, perm, chunk$186, addr$188);
    }
  }
}

unsigned int *check_mem(unsigned int perm$198, unsigned int chunk$200, unsigned int addr$202)
{
  _Bool well_chunk$204;
  unsigned int mem_reg_num;
  unsigned int *check_mem$208;
  well_chunk$204 = is_well_chunk_bool(chunk$200);
  if (well_chunk$204) {
    mem_reg_num = eval_mrs_num();
    check_mem$208 = check_mem_aux(mem_reg_num, perm$198, chunk$200, addr$202);
    if (check_mem$208 == 0) {
      return 0;
    } else {
      return check_mem$208;
    }
  } else {
    return 0;
  }
}

_Bool comp_and_0x08_byte(unsigned char x$210)
{
  return 0 == (x$210 & 8);
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64, unsigned int dst, unsigned char op$218)
{
  unsigned char opcode_alu64;
  unsigned int src32;
  unsigned int src32$224;
  unsigned int src32$226;
  unsigned int src32$228;
  opcode_alu64 = get_opcode_alu64(op$218);
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
      src32$224 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> src32$224);
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
      src32$226 = reg64_to_reg32(src64);
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % src32$226);
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
      src32$228 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> src32$228);
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$232, unsigned int dst$234, unsigned char op$236)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$236);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$234,
              (unsigned long long) (unsigned int) (dst32 + src32$232));
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst$234,
              (unsigned long long) (unsigned int) (dst32 - src32$232));
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst$234,
              (unsigned long long) (unsigned int) (dst32 * src32$232));
      upd_flag(0);
      return;
    case 48:
      if (src32$232 != 0U) {
        upd_reg(dst$234,
                (unsigned long long) (unsigned int) (dst32 / src32$232));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$234,
              (unsigned long long) (unsigned int) (dst32 | src32$232));
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst$234,
              (unsigned long long) (unsigned int) (dst32 & src32$232));
      upd_flag(0);
      return;
    case 96:
      if (src32$232 < 32U) {
        upd_reg(dst$234,
                (unsigned long long) (unsigned int) (dst32 << src32$232));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$232 < 32U) {
        upd_reg(dst$234,
                (unsigned long long) (unsigned int) (dst32 >> src32$232));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst$234, (unsigned long long) (unsigned int) -dst32);
      upd_flag(0);
      return;
    case 144:
      if (src32$232 != 0U) {
        upd_reg(dst$234,
                (unsigned long long) (unsigned int) (dst32 % src32$232));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$234,
              (unsigned long long) (unsigned int) (dst32 ^ src32$232));
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst$234, src32$232);
      upd_flag(0);
      return;
    case 192:
      if (src32$232 < 32U) {
        upd_reg(dst$234,
                (unsigned long long) (unsigned int) ((int) dst32
                                                      >> src32$232));
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

void step_opcode_branch(unsigned long long dst64$240, unsigned long long src64$242, int pc, int ofs$246, unsigned char op$248)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op$248);
  switch (opcode_jmp) {
    case 0:
      upd_pc(pc + ofs$246);
      upd_flag(0);
      return;
    case 16:
      if (dst64$240 == src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 32:
      if (dst64$240 > src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 48:
      if (dst64$240 >= src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 160:
      if (dst64$240 < src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 176:
      if (dst64$240 <= src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 64:
      if ((dst64$240 & src64$242) != 0LLU) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 80:
      if (dst64$240 != src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 96:
      if ((long long) dst64$240 > (long long) src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 112:
      if ((long long) dst64$240 >= (long long) src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 192:
      if ((long long) dst64$240 < (long long) src64$242) {
        upd_pc(pc + ofs$246);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 208:
      if ((long long) dst64$240 <= (long long) src64$242) {
        upd_pc(pc + ofs$246);
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

void step_opcode_mem_ld_imm(int imm, int pc$254, int len, unsigned int dst$258, unsigned char op$260, unsigned long long *l$262)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  opcode_ld = get_opcode_mem_ld_imm(op$260);
  switch (opcode_ld) {
    case 24:
      if (pc$254 + 1 < len) {
        next_ins = list_get(l$262, pc$254 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$258,
                (unsigned long long) imm
                  | (unsigned long long) next_imm << 32U);
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

void step_opcode_mem_ld_reg(unsigned int addr$270, int pc$272, unsigned int dst$274, unsigned char op$276)
{
  unsigned char opcode_ld$278;
  unsigned int *addr_ptr;
  unsigned long long v;
  unsigned int *addr_ptr$284;
  unsigned long long v$286;
  unsigned int *addr_ptr$288;
  unsigned long long v$290;
  unsigned int *addr_ptr$292;
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
        upd_flag(0);
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
        upd_flag(0);
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
        upd_flag(0);
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
        upd_flag(0);
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
  unsigned int *addr_ptr$308;
  unsigned int *addr_ptr$310;
  unsigned int *addr_ptr$312;
  unsigned int *addr_ptr$314;
  opcode_st = get_opcode_mem_st_imm(op$304);
  switch (opcode_st) {
    case 98:
      addr_ptr$308 = check_mem(2U, 4U, addr$298);
      if (addr_ptr$308 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$308, imm$296);
        upd_flag(0);
        return;
      }
    case 106:
      addr_ptr$310 = check_mem(2U, 2U, addr$298);
      if (addr_ptr$310 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$310, imm$296);
        upd_flag(0);
        return;
      }
    case 114:
      addr_ptr$312 = check_mem(2U, 1U, addr$298);
      if (addr_ptr$312 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$312, imm$296);
        upd_flag(0);
        return;
      }
    case 122:
      addr_ptr$314 = check_mem(2U, 8U, addr$298);
      if (addr_ptr$314 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$314, imm$296);
        upd_flag(0);
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
  unsigned int *addr_ptr$328;
  unsigned int *addr_ptr$330;
  unsigned int *addr_ptr$332;
  unsigned int *addr_ptr$334;
  opcode_st$326 = get_opcode_mem_st_reg(op$324);
  switch (opcode_st$326) {
    case 99:
      addr_ptr$328 = check_mem(2U, 4U, addr$318);
      if (addr_ptr$328 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$328, src64$316);
        upd_flag(0);
        return;
      }
    case 107:
      addr_ptr$330 = check_mem(2U, 2U, addr$318);
      if (addr_ptr$330 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$330, src64$316);
        upd_flag(0);
        return;
      }
    case 115:
      addr_ptr$332 = check_mem(2U, 1U, addr$318);
      if (addr_ptr$332 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$332, src64$316);
        upd_flag(0);
        return;
      }
    case 123:
      addr_ptr$334 = check_mem(2U, 8U, addr$318);
      if (addr_ptr$334 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$334, src64$316);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(int len$336, unsigned long long *l$338)
{
  int pc$340;
  unsigned long long ins$342;
  unsigned char op$344;
  unsigned char opc;
  unsigned int dst$348;
  unsigned long long dst64$350;
  _Bool is_imm;
  int imm$354;
  unsigned long long imm64;
  unsigned int src;
  unsigned long long src64$360;
  unsigned int dst$362;
  unsigned long long dst64$364;
  unsigned int dst32$366;
  _Bool is_imm$368;
  int imm$370;
  unsigned int src$372;
  unsigned long long src64$374;
  unsigned int src32$376;
  unsigned int dst$378;
  unsigned long long dst64$380;
  int ofs$382;
  _Bool is_imm$384;
  int imm$386;
  unsigned long long imm64$388;
  unsigned int src$390;
  unsigned long long src64$392;
  unsigned int dst$394;
  int imm$396;
  unsigned int dst$398;
  unsigned int src$400;
  unsigned long long src64$402;
  int ofs$404;
  unsigned int addr$406;
  unsigned int dst$408;
  unsigned long long dst64$410;
  int ofs$412;
  int imm$414;
  unsigned int addr$416;
  unsigned int dst$418;
  unsigned long long dst64$420;
  unsigned int src$422;
  unsigned long long src64$424;
  int ofs$426;
  unsigned int addr$428;
  pc$340 = eval_pc();
  ins$342 = list_get(l$338, pc$340);
  op$344 = get_opcode_ins(ins$342);
  opc = get_opcode(op$344);
  switch (opc) {
    case 7:
      dst$348 = get_dst(ins$342);
      dst64$350 = eval_reg(dst$348);
      is_imm = comp_and_0x08_byte(op$344);
      if (is_imm) {
        imm$354 = get_immediate(ins$342);
        imm64 = eval_immediate(imm$354);
        step_opcode_alu64(dst64$350, imm64, dst$348, op$344);
        return;
      } else {
        src = get_src(ins$342);
        src64$360 = eval_reg(src);
        step_opcode_alu64(dst64$350, src64$360, dst$348, op$344);
        return;
      }
    case 4:
      dst$362 = get_dst(ins$342);
      dst64$364 = eval_reg(dst$362);
      dst32$366 = reg64_to_reg32(dst64$364);
      is_imm$368 = comp_and_0x08_byte(op$344);
      if (is_imm$368) {
        imm$370 = get_immediate(ins$342);
        step_opcode_alu32(dst32$366, imm$370, dst$362, op$344);
        return;
      } else {
        src$372 = get_src(ins$342);
        src64$374 = eval_reg(src$372);
        src32$376 = reg64_to_reg32(src64$374);
        step_opcode_alu32(dst32$366, src32$376, dst$362, op$344);
        return;
      }
    case 5:
      dst$378 = get_dst(ins$342);
      dst64$380 = eval_reg(dst$378);
      ofs$382 = get_offset(ins$342);
      is_imm$384 = comp_and_0x08_byte(op$344);
      if (is_imm$384) {
        imm$386 = get_immediate(ins$342);
        imm64$388 = eval_immediate(imm$386);
        step_opcode_branch(dst64$380, imm64$388, pc$340, ofs$382, op$344);
        return;
      } else {
        src$390 = get_src(ins$342);
        src64$392 = eval_reg(src$390);
        step_opcode_branch(dst64$380, src64$392, pc$340, ofs$382, op$344);
        return;
      }
    case 0:
      dst$394 = get_dst(ins$342);
      imm$396 = get_immediate(ins$342);
      step_opcode_mem_ld_imm(imm$396, pc$340, len$336, dst$394, op$344,
                             l$338);
      return;
    case 1:
      dst$398 = get_dst(ins$342);
      src$400 = get_src(ins$342);
      src64$402 = eval_reg(src$400);
      ofs$404 = get_offset(ins$342);
      addr$406 = get_addr_ofs(src64$402, ofs$404);
      step_opcode_mem_ld_reg(addr$406, pc$340, dst$398, op$344);
      return;
    case 2:
      dst$408 = get_dst(ins$342);
      dst64$410 = eval_reg(dst$408);
      ofs$412 = get_offset(ins$342);
      imm$414 = get_immediate(ins$342);
      addr$416 = get_addr_ofs(dst64$410, ofs$412);
      step_opcode_mem_st_imm(imm$414, addr$416, pc$340, dst$408, op$344);
      return;
    case 3:
      dst$418 = get_dst(ins$342);
      dst64$420 = eval_reg(dst$418);
      src$422 = get_src(ins$342);
      src64$424 = eval_reg(src$422);
      ofs$426 = get_offset(ins$342);
      addr$428 = get_addr_ofs(dst64$420, ofs$426);
      step_opcode_mem_st_reg(src64$424, addr$428, pc$340, dst$418, op$344);
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


