struct memory_region;
struct bpf_state;
struct memory_region {
  unsigned int start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned int block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned int mem_num;
  unsigned long long regsmap[11];
  struct memory_region *mrs$757165;
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

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned int check_mem_aux2(struct memory_region *, unsigned int, unsigned int);

extern unsigned int check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned int);

extern unsigned int check_mem(unsigned int, unsigned int, unsigned int);

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

extern unsigned int eval_mem_num(void);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern struct memory_region *eval_mem_regions(void);

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

unsigned int get_src(unsigned long long ins$108)
{
  return (unsigned int) ((ins$108 & 65535LLU) >> 12LLU);
}

int get_offset(unsigned long long ins$110)
{
  return (int) (short) (ins$110 << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins$112)
{
  return (int) (ins$112 >> 32LLU);
}

unsigned long long eval_immediate(int ins$114)
{
  return (unsigned long long) ins$114;
}

unsigned char get_opcode_ins(unsigned long long ins$116)
{
  return (unsigned char) (ins$116 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$120)
{
  return (unsigned char) (op$120 & 240);
}

unsigned char get_opcode_branch(unsigned char op$122)
{
  return (unsigned char) (op$122 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$124)
{
  return (unsigned char) (op$124 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$126)
{
  return (unsigned char) (op$126 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$128)
{
  return (unsigned char) (op$128 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$130)
{
  return (unsigned char) (op$130 & 255);
}

unsigned char get_opcode(unsigned char op$132)
{
  return (unsigned char) (op$132 & 7);
}

unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}

unsigned int get_sub(unsigned int x$138, unsigned int y$140)
{
  return x$138 - y$140;
}

unsigned int get_addr_ofs(unsigned long long x$142, int ofs)
{
  return (unsigned int) (x$142 + (unsigned long long) ofs);
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

unsigned int check_mem_aux2(struct memory_region *mr, unsigned int addr, unsigned int chunk$152)
{
  _Bool well_chunk;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  well_chunk = is_well_chunk_bool(chunk$152);
  if (well_chunk) {
    lo_ofs = get_sub(addr, (*mr).start_addr);
    hi_ofs = get_add(lo_ofs, (unsigned int) chunk$152);
    if (0U <= lo_ofs && hi_ofs < (*mr).block_size) {
      if (lo_ofs <= 4294967295U - (unsigned int) chunk$152
            && 0U == lo_ofs % (unsigned int) chunk$152) {
        return (*mr).block_ptr + lo_ofs;
      } else {
        return 0U;
      }
    } else {
      return 0U;
    }
  } else {
    return 0U;
  }
}

unsigned int check_mem_aux(unsigned int num, unsigned int perm, unsigned int chunk$164, unsigned int addr$166)
{
  unsigned int n$168;
  struct memory_region *cur_mr;
  unsigned int check_mem$172;
  if (num == 0U) {
    return 0U;
  } else {
    n$168 = num - 1U;
    cur_mr = get_mem_region(n$168);
    if ((*cur_mr).block_perm >= perm) {
      check_mem$172 = check_mem_aux2(cur_mr, addr$166, chunk$164);
      if (check_mem$172 == 0U) {
        return check_mem_aux(n$168, perm, chunk$164, addr$166);
      } else {
        return check_mem$172;
      }
    } else {
      return check_mem_aux(n$168, perm, chunk$164, addr$166);
    }
  }
}

unsigned int check_mem(unsigned int perm$174, unsigned int chunk$176, unsigned int addr$178)
{
  _Bool well_chunk$180;
  unsigned int mem_reg_num;
  unsigned int check_mem$184;
  well_chunk$180 = is_well_chunk_bool(chunk$176);
  if (well_chunk$180) {
    mem_reg_num = eval_mem_num();
    check_mem$184 = check_mem_aux(mem_reg_num, perm$174, chunk$176, addr$178);
    if (check_mem$184 == 0U) {
      return 0U;
    } else {
      return check_mem$184;
    }
  } else {
    return 0U;
  }
}

_Bool comp_and_0x08_byte(unsigned char x$186)
{
  return 0 == (x$186 & 8);
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64, unsigned int dst, unsigned char op$194)
{
  unsigned char opcode_alu64;
  unsigned int src32;
  unsigned int src32$200;
  unsigned int src32$202;
  unsigned int src32$204;
  opcode_alu64 = get_opcode_alu64(op$194);
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
      src32$200 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> src32$200);
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
      src32$202 = reg64_to_reg32(src64);
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % src32$202);
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
      src32$204 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> src32$204);
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$208, unsigned int dst$210, unsigned char op$212)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$212);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$210, (unsigned long long) (dst32 + src32$208));
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst$210, (unsigned long long) (dst32 - src32$208));
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst$210, (unsigned long long) (dst32 * src32$208));
      upd_flag(0);
      return;
    case 48:
      if (src32$208 != 0U) {
        upd_reg(dst$210, (unsigned long long) (dst32 / src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$210, (unsigned long long) (dst32 | src32$208));
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst$210, (unsigned long long) (dst32 & src32$208));
      upd_flag(0);
      return;
    case 96:
      if (src32$208 < 32U) {
        upd_reg(dst$210, (unsigned long long) (dst32 << src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$208 < 32U) {
        upd_reg(dst$210, (unsigned long long) (dst32 >> src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst$210, (unsigned long long) -dst32);
      upd_flag(0);
      return;
    case 144:
      if (src32$208 != 0U) {
        upd_reg(dst$210, (unsigned long long) (dst32 % src32$208));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$210, (unsigned long long) (dst32 ^ src32$208));
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst$210, src32$208);
      upd_flag(0);
      return;
    case 192:
      if (src32$208 < 32U) {
        upd_reg(dst$210, (unsigned long long) ((int) dst32 >> src32$208));
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

void step_opcode_branch(unsigned long long dst64$216, unsigned long long src64$218, int pc, int ofs$222, unsigned char op$224)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op$224);
  switch (opcode_jmp) {
    case 0:
      upd_pc(pc + ofs$222);
      upd_flag(0);
      return;
    case 16:
      if (dst64$216 == src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 32:
      if (dst64$216 > src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 48:
      if (dst64$216 >= src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 160:
      if (dst64$216 < src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 176:
      if (dst64$216 <= src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 64:
      if ((dst64$216 & src64$218) != 0LLU) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 80:
      if (dst64$216 != src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 96:
      if ((long long) dst64$216 > (long long) src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 112:
      if ((long long) dst64$216 >= (long long) src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 192:
      if ((long long) dst64$216 < (long long) src64$218) {
        upd_pc(pc + ofs$222);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 208:
      if ((long long) dst64$216 <= (long long) src64$218) {
        upd_pc(pc + ofs$222);
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

void step_opcode_mem_ld_imm(int imm, int pc$230, int len, unsigned int dst$234, unsigned char op$236, unsigned long long *l$238)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  opcode_ld = get_opcode_mem_ld_imm(op$236);
  switch (opcode_ld) {
    case 24:
      if (pc$230 + 1 < len) {
        next_ins = list_get(l$238, pc$230 + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst$234,
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

void step_opcode_mem_ld_reg(unsigned int addr$246, int pc$248, unsigned int dst$250, unsigned char op$252)
{
  unsigned char opcode_ld$254;
  unsigned int addr_ptr;
  unsigned long long v;
  unsigned int addr_ptr$260;
  unsigned long long v$262;
  unsigned int addr_ptr$264;
  unsigned long long v$266;
  unsigned int addr_ptr$268;
  unsigned long long v$270;
  opcode_ld$254 = get_opcode_mem_ld_reg(op$252);
  switch (opcode_ld$254) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$246);
      if (addr_ptr == 0U) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$250, v);
        upd_flag(0);
        return;
      }
    case 105:
      addr_ptr$260 = check_mem(1U, 2U, addr$246);
      if (addr_ptr$260 == 0U) {
        upd_flag(-2);
        return;
      } else {
        v$262 = load_mem(2U, addr_ptr$260);
        upd_reg(dst$250, v$262);
        upd_flag(0);
        return;
      }
    case 113:
      addr_ptr$264 = check_mem(1U, 1U, addr$246);
      if (addr_ptr$264 == 0U) {
        upd_flag(-2);
        return;
      } else {
        v$266 = load_mem(1U, addr_ptr$264);
        upd_reg(dst$250, v$266);
        upd_flag(0);
        return;
      }
    case 121:
      addr_ptr$268 = check_mem(1U, 8U, addr$246);
      if (addr_ptr$268 == 0U) {
        upd_flag(-2);
        return;
      } else {
        v$270 = load_mem(8U, addr_ptr$268);
        upd_reg(dst$250, v$270);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$272, unsigned int addr$274, int pc$276, unsigned int dst$278, unsigned char op$280)
{
  unsigned char opcode_st;
  unsigned int addr_ptr$284;
  unsigned int addr_ptr$286;
  unsigned int addr_ptr$288;
  unsigned int addr_ptr$290;
  opcode_st = get_opcode_mem_st_imm(op$280);
  switch (opcode_st) {
    case 98:
      addr_ptr$284 = check_mem(2U, 4U, addr$274);
      if (addr_ptr$284 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, addr_ptr$284, imm$272);
        upd_flag(0);
        return;
      }
    case 106:
      addr_ptr$286 = check_mem(2U, 2U, addr$274);
      if (addr_ptr$286 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, addr_ptr$286, imm$272);
        upd_flag(0);
        return;
      }
    case 114:
      addr_ptr$288 = check_mem(2U, 1U, addr$274);
      if (addr_ptr$288 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, addr_ptr$288, imm$272);
        upd_flag(0);
        return;
      }
    case 122:
      addr_ptr$290 = check_mem(2U, 8U, addr$274);
      if (addr_ptr$290 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, addr_ptr$290, imm$272);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$292, unsigned int addr$294, int pc$296, unsigned int dst$298, unsigned char op$300)
{
  unsigned char opcode_st$302;
  unsigned int addr_ptr$304;
  unsigned int addr_ptr$306;
  unsigned int addr_ptr$308;
  unsigned int addr_ptr$310;
  opcode_st$302 = get_opcode_mem_st_reg(op$300);
  switch (opcode_st$302) {
    case 99:
      addr_ptr$304 = check_mem(2U, 4U, addr$294);
      if (addr_ptr$304 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, addr_ptr$304, src64$292);
        upd_flag(0);
        return;
      }
    case 107:
      addr_ptr$306 = check_mem(2U, 2U, addr$294);
      if (addr_ptr$306 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, addr_ptr$306, src64$292);
        upd_flag(0);
        return;
      }
    case 115:
      addr_ptr$308 = check_mem(2U, 1U, addr$294);
      if (addr_ptr$308 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, addr_ptr$308, src64$292);
        upd_flag(0);
        return;
      }
    case 123:
      addr_ptr$310 = check_mem(2U, 8U, addr$294);
      if (addr_ptr$310 == 0U) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, addr_ptr$310, src64$292);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(int len$312, unsigned long long *l$314)
{
  int pc$316;
  unsigned long long ins$318;
  unsigned char op$320;
  unsigned char opc;
  unsigned int dst$324;
  unsigned long long dst64$326;
  _Bool is_imm;
  int imm$330;
  unsigned long long imm64;
  unsigned int src;
  unsigned long long src64$336;
  unsigned int dst$338;
  unsigned long long dst64$340;
  unsigned int dst32$342;
  _Bool is_imm$344;
  int imm$346;
  unsigned int src$348;
  unsigned long long src64$350;
  unsigned int src32$352;
  unsigned int dst$354;
  unsigned long long dst64$356;
  int ofs$358;
  _Bool is_imm$360;
  int imm$362;
  unsigned long long imm64$364;
  unsigned int src$366;
  unsigned long long src64$368;
  unsigned int dst$370;
  int imm$372;
  unsigned int dst$374;
  unsigned int src$376;
  unsigned long long src64$378;
  int ofs$380;
  unsigned int addr$382;
  unsigned int dst$384;
  unsigned long long dst64$386;
  int ofs$388;
  int imm$390;
  unsigned int addr$392;
  unsigned int dst$394;
  unsigned long long dst64$396;
  unsigned int src$398;
  unsigned long long src64$400;
  int ofs$402;
  unsigned int addr$404;
  pc$316 = eval_pc();
  ins$318 = list_get(l$314, pc$316);
  op$320 = get_opcode_ins(ins$318);
  opc = get_opcode(op$320);
  switch (opc) {
    case 7:
      dst$324 = get_dst(ins$318);
      dst64$326 = eval_reg(dst$324);
      is_imm = comp_and_0x08_byte(op$320);
      if (is_imm) {
        imm$330 = get_immediate(ins$318);
        imm64 = eval_immediate(imm$330);
        step_opcode_alu64(dst64$326, imm64, dst$324, op$320);
        return;
      } else {
        src = get_src(ins$318);
        src64$336 = eval_reg(src);
        step_opcode_alu64(dst64$326, src64$336, dst$324, op$320);
        return;
      }
    case 4:
      dst$338 = get_dst(ins$318);
      dst64$340 = eval_reg(dst$338);
      dst32$342 = reg64_to_reg32(dst64$340);
      is_imm$344 = comp_and_0x08_byte(op$320);
      if (is_imm$344) {
        imm$346 = get_immediate(ins$318);
        step_opcode_alu32(dst32$342, imm$346, dst$338, op$320);
        return;
      } else {
        src$348 = get_src(ins$318);
        src64$350 = eval_reg(src$348);
        src32$352 = reg64_to_reg32(src64$350);
        step_opcode_alu32(dst32$342, src32$352, dst$338, op$320);
        return;
      }
    case 5:
      dst$354 = get_dst(ins$318);
      dst64$356 = eval_reg(dst$354);
      ofs$358 = get_offset(ins$318);
      is_imm$360 = comp_and_0x08_byte(op$320);
      if (is_imm$360) {
        imm$362 = get_immediate(ins$318);
        imm64$364 = eval_immediate(imm$362);
        step_opcode_branch(dst64$356, imm64$364, pc$316, ofs$358, op$320);
        return;
      } else {
        src$366 = get_src(ins$318);
        src64$368 = eval_reg(src$366);
        step_opcode_branch(dst64$356, src64$368, pc$316, ofs$358, op$320);
        return;
      }
    case 0:
      dst$370 = get_dst(ins$318);
      imm$372 = get_immediate(ins$318);
      step_opcode_mem_ld_imm(imm$372, pc$316, len$312, dst$370, op$320,
                             l$314);
      return;
    case 1:
      dst$374 = get_dst(ins$318);
      src$376 = get_src(ins$318);
      src64$378 = eval_reg(src$376);
      ofs$380 = get_offset(ins$318);
      addr$382 = get_addr_ofs(src64$378, ofs$380);
      step_opcode_mem_ld_reg(addr$382, pc$316, dst$374, op$320);
      return;
    case 2:
      dst$384 = get_dst(ins$318);
      dst64$386 = eval_reg(dst$384);
      ofs$388 = get_offset(ins$318);
      imm$390 = get_immediate(ins$318);
      addr$392 = get_addr_ofs(dst64$386, ofs$388);
      step_opcode_mem_st_imm(imm$390, addr$392, pc$316, dst$384, op$320);
      return;
    case 3:
      dst$394 = get_dst(ins$318);
      dst64$396 = eval_reg(dst$394);
      src$398 = get_src(ins$318);
      src64$400 = eval_reg(src$398);
      ofs$402 = get_offset(ins$318);
      addr$404 = get_addr_ofs(dst64$396, ofs$402);
      step_opcode_mem_st_reg(src64$400, addr$404, pc$316, dst$394, op$320);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(int len$406, unsigned int fuel, unsigned long long *l$410)
{
  unsigned int fuel0;
  int pc$414;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    pc$414 = eval_pc();
    if (0U <= pc$414 && pc$414 < len$406) {
      step(len$406, l$410);
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
        bpf_interpreter_aux(len$406, fuel0, l$410);
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

unsigned long long bpf_interpreter(int len$418, unsigned int fuel$420, unsigned long long *l$422)
{
  struct memory_region *bpf_ctx;
  int f$426;
  bpf_ctx = get_mem_region(0U);
  upd_reg(1U, (*bpf_ctx).start_addr);
  bpf_interpreter_aux(len$418, fuel$420, l$422);
  f$426 = eval_flag();
  if (f$426 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


