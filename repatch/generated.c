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

extern _Bool step_opcode_branch(unsigned long long, unsigned long long, unsigned char);

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
  opcode_alu64 = get_opcode_alu64(op$218);
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
      src32$224 = reg64_to_reg32(src64);
      if (src32$224 < 64U) {
        upd_reg(dst, dst64 >> src32$224);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$218 == 135) {
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
      src32$226 = reg64_to_reg32(src64);
      if (src32$226 < 64U) {
        upd_reg(dst, (long long) dst64 >> src32$226);
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$230, unsigned int dst$232, unsigned char op$234)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$234);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$232,
              (unsigned long long) (unsigned int) (dst32 + src32$230));
      return;
    case 16:
      upd_reg(dst$232,
              (unsigned long long) (unsigned int) (dst32 - src32$230));
      return;
    case 32:
      upd_reg(dst$232,
              (unsigned long long) (unsigned int) (dst32 * src32$230));
      return;
    case 48:
      if (src32$230 != 0U) {
        upd_reg(dst$232,
                (unsigned long long) (unsigned int) (dst32 / src32$230));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$232,
              (unsigned long long) (unsigned int) (dst32 | src32$230));
      return;
    case 80:
      upd_reg(dst$232,
              (unsigned long long) (unsigned int) (dst32 & src32$230));
      return;
    case 96:
      if (src32$230 < 32U) {
        upd_reg(dst$232,
                (unsigned long long) (unsigned int) (dst32 << src32$230));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$230 < 32U) {
        upd_reg(dst$232,
                (unsigned long long) (unsigned int) (dst32 >> src32$230));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$234 == 132) {
        upd_reg(dst$232, (unsigned long long) (unsigned int) -dst32);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src32$230 != 0U) {
        upd_reg(dst$232,
                (unsigned long long) (unsigned int) (dst32 % src32$230));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$232,
              (unsigned long long) (unsigned int) (dst32 ^ src32$230));
      return;
    case 176:
      upd_reg(dst$232, (unsigned long long) (unsigned int) src32$230);
      return;
    case 192:
      if (src32$230 < 32U) {
        upd_reg(dst$232,
                (unsigned long long) (unsigned int) ((int) dst32
                                                      >> src32$230));
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

_Bool step_opcode_branch(unsigned long long dst64$238, unsigned long long src64$240, unsigned char op$242)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op$242);
  switch (opcode_jmp) {
    case 0:
      if (op$242 == 5) {
        return 1;
      } else {
        upd_flag(-1);
        return 0;
      }
    case 16:
      return dst64$238 == src64$240;
    case 32:
      return dst64$238 > src64$240;
    case 48:
      return dst64$238 >= src64$240;
    case 160:
      return dst64$238 < src64$240;
    case 176:
      return dst64$238 <= src64$240;
    case 64:
      return (dst64$238 & src64$240) != 0LLU;
    case 80:
      return dst64$238 != src64$240;
    case 96:
      return (long long) dst64$238 > (long long) src64$240;
    case 112:
      return (long long) dst64$238 >= (long long) src64$240;
    case 192:
      return (long long) dst64$238 < (long long) src64$240;
    case 208:
      return (long long) dst64$238 <= (long long) src64$240;
    case 144:
      if (op$242 == 149) {
        upd_flag(1);
        return 0;
      } else {
        return 0;
      }
    default:
      upd_flag(-1);
      return 0;
    
  }
}

void step_opcode_mem_ld_imm(int imm, int pc, unsigned int dst$250, unsigned char op$252)
{
  int len;
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  len = eval_ins_len();
  opcode_ld = get_opcode_mem_ld_imm(op$252);
  switch (opcode_ld) {
    case 24:
      if (pc + 1 < len) {
        next_ins = eval_ins(pc + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$250,
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

void step_opcode_mem_ld_reg(unsigned int addr$262, int pc$264, unsigned int dst$266, unsigned char op$268)
{
  unsigned char opcode_ld$270;
  unsigned char *addr_ptr;
  unsigned long long v;
  unsigned char *addr_ptr$276;
  unsigned long long v$278;
  unsigned char *addr_ptr$280;
  unsigned long long v$282;
  unsigned char *addr_ptr$284;
  unsigned long long v$286;
  opcode_ld$270 = get_opcode_mem_ld_reg(op$268);
  switch (opcode_ld$270) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$262);
      if (addr_ptr == 0) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$266, v);
        return;
      }
    case 105:
      addr_ptr$276 = check_mem(1U, 2U, addr$262);
      if (addr_ptr$276 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$278 = load_mem(2U, addr_ptr$276);
        upd_reg(dst$266, v$278);
        return;
      }
    case 113:
      addr_ptr$280 = check_mem(1U, 1U, addr$262);
      if (addr_ptr$280 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$282 = load_mem(1U, addr_ptr$280);
        upd_reg(dst$266, v$282);
        return;
      }
    case 121:
      addr_ptr$284 = check_mem(1U, 8U, addr$262);
      if (addr_ptr$284 == 0) {
        upd_flag(-2);
        return;
      } else {
        v$286 = load_mem(8U, addr_ptr$284);
        upd_reg(dst$266, v$286);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$288, unsigned int addr$290, int pc$292, unsigned int dst$294, unsigned char op$296)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$300;
  unsigned char *addr_ptr$302;
  unsigned char *addr_ptr$304;
  unsigned char *addr_ptr$306;
  opcode_st = get_opcode_mem_st_imm(op$296);
  switch (opcode_st) {
    case 98:
      addr_ptr$300 = check_mem(2U, 4U, addr$290);
      if (addr_ptr$300 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$300, imm$288);
        return;
      }
    case 106:
      addr_ptr$302 = check_mem(2U, 2U, addr$290);
      if (addr_ptr$302 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$302, imm$288);
        return;
      }
    case 114:
      addr_ptr$304 = check_mem(2U, 1U, addr$290);
      if (addr_ptr$304 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$304, imm$288);
        return;
      }
    case 122:
      addr_ptr$306 = check_mem(2U, 8U, addr$290);
      if (addr_ptr$306 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$306, imm$288);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$308, unsigned int addr$310, int pc$312, unsigned int dst$314, unsigned char op$316)
{
  unsigned char opcode_st$318;
  unsigned char *addr_ptr$320;
  unsigned char *addr_ptr$322;
  unsigned char *addr_ptr$324;
  unsigned char *addr_ptr$326;
  opcode_st$318 = get_opcode_mem_st_reg(op$316);
  switch (opcode_st$318) {
    case 99:
      addr_ptr$320 = check_mem(2U, 4U, addr$310);
      if (addr_ptr$320 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$320, src64$308);
        return;
      }
    case 107:
      addr_ptr$322 = check_mem(2U, 2U, addr$310);
      if (addr_ptr$322 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$322, src64$308);
        return;
      }
    case 115:
      addr_ptr$324 = check_mem(2U, 1U, addr$310);
      if (addr_ptr$324 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$324, src64$308);
        return;
      }
    case 123:
      addr_ptr$326 = check_mem(2U, 8U, addr$310);
      if (addr_ptr$326 == 0) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$326, src64$308);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  int pc$328;
  unsigned long long ins$330;
  unsigned char op$332;
  unsigned char opc;
  unsigned int dst$336;
  unsigned long long dst64$338;
  _Bool is_imm;
  int imm$342;
  unsigned long long imm64;
  unsigned int src;
  unsigned long long src64$348;
  unsigned int dst$350;
  unsigned long long dst64$352;
  unsigned int dst32$354;
  _Bool is_imm$356;
  int imm$358;
  unsigned int src$360;
  unsigned long long src64$362;
  unsigned int src32$364;
  unsigned int dst$366;
  unsigned long long dst64$368;
  int ofs$370;
  _Bool is_imm$372;
  int imm$374;
  unsigned long long imm64$376;
  _Bool res;
  unsigned int src$380;
  unsigned long long src64$382;
  _Bool res$384;
  unsigned int dst$386;
  int imm$388;
  unsigned int dst$390;
  unsigned int src$392;
  unsigned long long src64$394;
  int ofs$396;
  unsigned int addr$398;
  unsigned int dst$400;
  unsigned long long dst64$402;
  int ofs$404;
  int imm$406;
  unsigned int addr$408;
  unsigned int dst$410;
  unsigned long long dst64$412;
  unsigned int src$414;
  unsigned long long src64$416;
  int ofs$418;
  unsigned int addr$420;
  pc$328 = eval_pc();
  ins$330 = eval_ins(pc$328);
  op$332 = get_opcode_ins(ins$330);
  opc = get_opcode(op$332);
  switch (opc) {
    case 7:
      dst$336 = get_dst(ins$330);
      dst64$338 = eval_reg(dst$336);
      is_imm = comp_and_0x08_byte(op$332);
      if (is_imm) {
        imm$342 = get_immediate(ins$330);
        imm64 = eval_immediate(imm$342);
        step_opcode_alu64(dst64$338, imm64, dst$336, op$332);
        return;
      } else {
        src = get_src(ins$330);
        src64$348 = eval_reg(src);
        step_opcode_alu64(dst64$338, src64$348, dst$336, op$332);
        return;
      }
    case 4:
      dst$350 = get_dst(ins$330);
      dst64$352 = eval_reg(dst$350);
      dst32$354 = reg64_to_reg32(dst64$352);
      is_imm$356 = comp_and_0x08_byte(op$332);
      if (is_imm$356) {
        imm$358 = get_immediate(ins$330);
        step_opcode_alu32(dst32$354, imm$358, dst$350, op$332);
        return;
      } else {
        src$360 = get_src(ins$330);
        src64$362 = eval_reg(src$360);
        src32$364 = reg64_to_reg32(src64$362);
        step_opcode_alu32(dst32$354, src32$364, dst$350, op$332);
        return;
      }
    case 5:
      dst$366 = get_dst(ins$330);
      dst64$368 = eval_reg(dst$366);
      ofs$370 = get_offset(ins$330);
      is_imm$372 = comp_and_0x08_byte(op$332);
      if (is_imm$372) {
        imm$374 = get_immediate(ins$330);
        imm64$376 = eval_immediate(imm$374);
        res = step_opcode_branch(dst64$368, imm64$376, op$332);
        if (res) {
          upd_pc(pc$328 + ofs$370);
          return;
        } else {
          return;
        }
      } else {
        src$380 = get_src(ins$330);
        src64$382 = eval_reg(src$380);
        res$384 = step_opcode_branch(dst64$368, src64$382, op$332);
        if (res$384) {
          upd_pc(pc$328 + ofs$370);
          return;
        } else {
          return;
        }
      }
    case 0:
      dst$386 = get_dst(ins$330);
      imm$388 = get_immediate(ins$330);
      step_opcode_mem_ld_imm(imm$388, pc$328, dst$386, op$332);
      return;
    case 1:
      dst$390 = get_dst(ins$330);
      src$392 = get_src(ins$330);
      src64$394 = eval_reg(src$392);
      ofs$396 = get_offset(ins$330);
      addr$398 = get_addr_ofs(src64$394, ofs$396);
      step_opcode_mem_ld_reg(addr$398, pc$328, dst$390, op$332);
      return;
    case 2:
      dst$400 = get_dst(ins$330);
      dst64$402 = eval_reg(dst$400);
      ofs$404 = get_offset(ins$330);
      imm$406 = get_immediate(ins$330);
      addr$408 = get_addr_ofs(dst64$402, ofs$404);
      step_opcode_mem_st_imm(imm$406, addr$408, pc$328, dst$400, op$332);
      return;
    case 3:
      dst$410 = get_dst(ins$330);
      dst64$412 = eval_reg(dst$410);
      src$414 = get_src(ins$330);
      src64$416 = eval_reg(src$414);
      ofs$418 = get_offset(ins$330);
      addr$420 = get_addr_ofs(dst64$412, ofs$418);
      step_opcode_mem_st_reg(src64$416, addr$420, pc$328, dst$410, op$332);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  int len$426;
  int pc$428;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len$426 = eval_ins_len();
    pc$428 = eval_pc();
    if (0U <= pc$428 && pc$428 < len$426) {
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

unsigned long long bpf_interpreter(unsigned int fuel$432)
{
  struct memory_region *bpf_ctx;
  int f$436;
  bpf_ctx = get_mem_region(0U);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(fuel$432);
  f$436 = eval_flag();
  if (f$436 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


