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
  struct memory_region *mrs$757165;
  unsigned int mrs_num;
  int ins_len;
  unsigned long long *ins$756645;
};

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

extern unsigned char *get_block_ptr(struct memory_region *);

extern unsigned int get_start_addr(struct memory_region *);

extern unsigned int get_block_size(struct memory_region *);

extern unsigned int get_block_perm(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned char *check_mem_aux2(struct memory_region *, unsigned int, unsigned int, unsigned int);

extern unsigned char *check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned int);

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

unsigned long long eval_immediate(int ins$120)
{
  return (unsigned long long) (unsigned int) ins$120;
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

unsigned char *check_mem_aux(unsigned int num, unsigned int perm$186, unsigned int chunk$188, unsigned int addr$190)
{
  unsigned int n$192;
  struct memory_region *cur_mr;
  unsigned char *check_mem$196;
  if (num == 0U) {
    return 0;
  } else {
    n$192 = num - 1U;
    cur_mr = get_mem_region(n$192);
    check_mem$196 = check_mem_aux2(cur_mr, perm$186, addr$190, chunk$188);
    if (check_mem$196 == 0) {
      return check_mem_aux(n$192, perm$186, chunk$188, addr$190);
    } else {
      return check_mem$196;
    }
  }
}

unsigned char *check_mem(unsigned int perm$198, unsigned int chunk$200, unsigned int addr$202)
{
  _Bool well_chunk$204;
  unsigned int mem_reg_num;
  unsigned char *check_mem$208;
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

void step_opcode_mem_ld_imm(int imm, int pc$254, unsigned int dst$256, unsigned char op$258)
{
  int len;
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  len = eval_ins_len();
  opcode_ld = get_opcode_mem_ld_imm(op$258);
  switch (opcode_ld) {
    case 24:
      if (pc$254 + 1 < len) {
        next_ins = eval_ins(pc$254 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$256,
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

void step_opcode_mem_ld_reg(unsigned int addr$268, int pc$270, unsigned int dst$272, unsigned char op$274)
{
  unsigned char opcode_ld$276;
  unsigned char *addr_ptr;
  unsigned long long v;
  unsigned char *addr_ptr$282;
  unsigned long long v$284;
  unsigned char *addr_ptr$286;
  unsigned long long v$288;
  unsigned char *addr_ptr$290;
  unsigned long long v$292;
  opcode_ld$276 = get_opcode_mem_ld_reg(op$274);
  switch (opcode_ld$276) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$268);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$272, v);
        upd_flag(0);
        return;
      }
    case 105:
      addr_ptr$282 = check_mem(1U, 2U, addr$268);
      if (addr_ptr$282 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$284 = load_mem(2U, addr_ptr$282);
        upd_reg(dst$272, v$284);
        upd_flag(0);
        return;
      }
    case 113:
      addr_ptr$286 = check_mem(1U, 1U, addr$268);
      if (addr_ptr$286 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$288 = load_mem(1U, addr_ptr$286);
        upd_reg(dst$272, v$288);
        upd_flag(0);
        return;
      }
    case 121:
      addr_ptr$290 = check_mem(1U, 8U, addr$268);
      if (addr_ptr$290 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$292 = load_mem(8U, addr_ptr$290);
        upd_reg(dst$272, v$292);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$294, unsigned int addr$296, int pc$298, unsigned int dst$300, unsigned char op$302)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$306;
  unsigned char *addr_ptr$308;
  unsigned char *addr_ptr$310;
  unsigned char *addr_ptr$312;
  opcode_st = get_opcode_mem_st_imm(op$302);
  switch (opcode_st) {
    case 98:
      addr_ptr$306 = check_mem(2U, 4U, addr$296);
      if (addr_ptr$306 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$306, imm$294);
        upd_flag(0);
        return;
      }
    case 106:
      addr_ptr$308 = check_mem(2U, 2U, addr$296);
      if (addr_ptr$308 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$308, imm$294);
        upd_flag(0);
        return;
      }
    case 114:
      addr_ptr$310 = check_mem(2U, 1U, addr$296);
      if (addr_ptr$310 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$310, imm$294);
        upd_flag(0);
        return;
      }
    case 122:
      addr_ptr$312 = check_mem(2U, 8U, addr$296);
      if (addr_ptr$312 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$312, imm$294);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$314, unsigned int addr$316, int pc$318, unsigned int dst$320, unsigned char op$322)
{
  unsigned char opcode_st$324;
  unsigned char *addr_ptr$326;
  unsigned char *addr_ptr$328;
  unsigned char *addr_ptr$330;
  unsigned char *addr_ptr$332;
  opcode_st$324 = get_opcode_mem_st_reg(op$322);
  switch (opcode_st$324) {
    case 99:
      addr_ptr$326 = check_mem(2U, 4U, addr$316);
      if (addr_ptr$326 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$326, src64$314);
        upd_flag(0);
        return;
      }
    case 107:
      addr_ptr$328 = check_mem(2U, 2U, addr$316);
      if (addr_ptr$328 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$328, src64$314);
        upd_flag(0);
        return;
      }
    case 115:
      addr_ptr$330 = check_mem(2U, 1U, addr$316);
      if (addr_ptr$330 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$330, src64$314);
        upd_flag(0);
        return;
      }
    case 123:
      addr_ptr$332 = check_mem(2U, 8U, addr$316);
      if (addr_ptr$332 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$332, src64$314);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  int pc$334;
  unsigned long long ins$336;
  unsigned char op$338;
  unsigned char opc;
  unsigned int dst$342;
  unsigned long long dst64$344;
  _Bool is_imm;
  int imm$348;
  unsigned long long imm64;
  unsigned int src;
  unsigned long long src64$354;
  unsigned int dst$356;
  unsigned long long dst64$358;
  unsigned int dst32$360;
  _Bool is_imm$362;
  int imm$364;
  unsigned int src$366;
  unsigned long long src64$368;
  unsigned int src32$370;
  unsigned int dst$372;
  unsigned long long dst64$374;
  int ofs$376;
  _Bool is_imm$378;
  int imm$380;
  unsigned long long imm64$382;
  unsigned int src$384;
  unsigned long long src64$386;
  unsigned int dst$388;
  int imm$390;
  unsigned int dst$392;
  unsigned int src$394;
  unsigned long long src64$396;
  int ofs$398;
  unsigned int addr$400;
  unsigned int dst$402;
  unsigned long long dst64$404;
  int ofs$406;
  int imm$408;
  unsigned int addr$410;
  unsigned int dst$412;
  unsigned long long dst64$414;
  unsigned int src$416;
  unsigned long long src64$418;
  int ofs$420;
  unsigned int addr$422;
  pc$334 = eval_pc();
  ins$336 = eval_ins(pc$334);
  op$338 = get_opcode_ins(ins$336);
  opc = get_opcode(op$338);
  switch (opc) {
    case 7:
      dst$342 = get_dst(ins$336);
      dst64$344 = eval_reg(dst$342);
      is_imm = comp_and_0x08_byte(op$338);
      if (is_imm) {
        imm$348 = get_immediate(ins$336);
        imm64 = eval_immediate(imm$348);
        step_opcode_alu64(dst64$344, imm64, dst$342, op$338);
        return;
      } else {
        src = get_src(ins$336);
        src64$354 = eval_reg(src);
        step_opcode_alu64(dst64$344, src64$354, dst$342, op$338);
        return;
      }
    case 4:
      dst$356 = get_dst(ins$336);
      dst64$358 = eval_reg(dst$356);
      dst32$360 = reg64_to_reg32(dst64$358);
      is_imm$362 = comp_and_0x08_byte(op$338);
      if (is_imm$362) {
        imm$364 = get_immediate(ins$336);
        step_opcode_alu32(dst32$360, imm$364, dst$356, op$338);
        return;
      } else {
        src$366 = get_src(ins$336);
        src64$368 = eval_reg(src$366);
        src32$370 = reg64_to_reg32(src64$368);
        step_opcode_alu32(dst32$360, src32$370, dst$356, op$338);
        return;
      }
    case 5:
      dst$372 = get_dst(ins$336);
      dst64$374 = eval_reg(dst$372);
      ofs$376 = get_offset(ins$336);
      is_imm$378 = comp_and_0x08_byte(op$338);
      if (is_imm$378) {
        imm$380 = get_immediate(ins$336);
        imm64$382 = eval_immediate(imm$380);
        step_opcode_branch(dst64$374, imm64$382, pc$334, ofs$376, op$338);
        return;
      } else {
        src$384 = get_src(ins$336);
        src64$386 = eval_reg(src$384);
        step_opcode_branch(dst64$374, src64$386, pc$334, ofs$376, op$338);
        return;
      }
    case 0:
      dst$388 = get_dst(ins$336);
      imm$390 = get_immediate(ins$336);
      step_opcode_mem_ld_imm(imm$390, pc$334, dst$388, op$338);
      return;
    case 1:
      dst$392 = get_dst(ins$336);
      src$394 = get_src(ins$336);
      src64$396 = eval_reg(src$394);
      ofs$398 = get_offset(ins$336);
      addr$400 = get_addr_ofs(src64$396, ofs$398);
      step_opcode_mem_ld_reg(addr$400, pc$334, dst$392, op$338);
      return;
    case 2:
      dst$402 = get_dst(ins$336);
      dst64$404 = eval_reg(dst$402);
      ofs$406 = get_offset(ins$336);
      imm$408 = get_immediate(ins$336);
      addr$410 = get_addr_ofs(dst64$404, ofs$406);
      step_opcode_mem_st_imm(imm$408, addr$410, pc$334, dst$402, op$338);
      return;
    case 3:
      dst$412 = get_dst(ins$336);
      dst64$414 = eval_reg(dst$412);
      src$416 = get_src(ins$336);
      src64$418 = eval_reg(src$416);
      ofs$420 = get_offset(ins$336);
      addr$422 = get_addr_ofs(dst64$414, ofs$420);
      step_opcode_mem_st_reg(src64$418, addr$422, pc$334, dst$412, op$338);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  int len$428;
  int pc$430;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len$428 = eval_ins_len();
    pc$430 = eval_pc();
    if (0U <= pc$430 && pc$430 < len$428) {
      step();
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
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

unsigned long long bpf_interpreter(unsigned int fuel$434)
{
  struct memory_region *bpf_ctx;
  int f$438;
  bpf_ctx = get_mem_region(0U);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(fuel$434);
  f$438 = eval_flag();
  if (f$438 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


