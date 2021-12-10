struct memory_region;
struct memory_regions;
struct bpf_state;
struct memory_region {
  unsigned long long start_addr;
  unsigned long long block_size;
  unsigned long long block_ptr;
};

struct memory_regions {
  struct memory_region *bpf_ctx;
  struct memory_region *bpf_stk;
  struct memory_region *content;
};

struct bpf_state {
  unsigned int state_pc;
  unsigned long long regsmap[11];
  int bpf_flag;
  struct memory_regions *mrs$757165;
};

extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned int get_dst(unsigned long long);

extern unsigned int reg64_to_reg32(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern unsigned long long get_offset(unsigned long long);

extern unsigned long long eval_offset(unsigned long long);

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

extern unsigned long long getMemRegion_block_ptr(struct memory_region *);

extern unsigned long long getMemRegion_start_addr(struct memory_region *);

extern unsigned long long getMemRegion_block_size(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned long long check_mem_aux(struct memory_region *, unsigned long long, unsigned int);

extern unsigned long long check_mem(unsigned long long *, unsigned long long, unsigned int);

extern _Bool comp_and_0x08_byte(unsigned char);

extern void step_opcode_alu64(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char);

extern void step_opcode_alu32(unsigned long long, unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_branch(unsigned long long, unsigned long long, unsigned long long, unsigned char, unsigned long long);

extern void step_opcode_mem_ld_imm(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long *);

extern void step_opcode_mem_ld_reg(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long, unsigned long long *);

extern void step_opcode_mem_st_imm(unsigned long long, unsigned int, unsigned long long, int, unsigned char, unsigned long long, unsigned long long, unsigned long long *);

extern void step_opcode_mem_st_reg(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long, unsigned long long *);

extern void step(unsigned long long, unsigned long long *);

extern void bpf_interpreter_aux(unsigned long long, unsigned int, unsigned long long *);

extern unsigned long long bpf_interpreter(unsigned long long, unsigned int, unsigned long long *);

extern unsigned long long eval_pc(void);

extern void upd_pc(unsigned long long);

extern void upd_pc_incr(void);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern int eval_flag(void);

extern void upd_flag(int);

extern struct memory_regions *eval_mem_regions(void);

extern void upd_mem_regions(struct memory_regions *);

extern unsigned long long load_mem(unsigned int, unsigned long long);

extern void store_mem_imm(unsigned int, unsigned long long, int);

extern void store_mem_reg(unsigned int, unsigned long long, unsigned long long);

unsigned long long list_get(unsigned long long *l, unsigned long long idx)
{
  return *(l + idx);
}

unsigned int get_dst(unsigned long long ins)
{
  return (unsigned int) ((ins & 4095LLU) >> 8LLU);
}

unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

unsigned int get_src(unsigned long long ins$106)
{
  return (unsigned int) ((ins$106 & 65535LLU) >> 12LLU);
}

unsigned long long get_offset(unsigned long long ins$108)
{
  return ins$108 << 32LLU >> 48LLU;
}

unsigned long long eval_offset(unsigned long long ins$110)
{
  return ins$110;
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

unsigned long long get_addl(unsigned long long x, unsigned long long y)
{
  return x + y;
}

unsigned long long get_subl(unsigned long long x$138, unsigned long long y$140)
{
  return x$138 - y$140;
}

unsigned long long getMemRegion_block_ptr(struct memory_region *mr)
{
  return 1LLU;
}

unsigned long long getMemRegion_start_addr(struct memory_region *mr$144)
{
  return (*mr$144).start_addr;
}

unsigned long long getMemRegion_block_size(struct memory_region *mr$146)
{
  return (*mr$146).block_size;
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

unsigned long long check_mem_aux(struct memory_region *mr$150, unsigned long long addr, unsigned int chunk$154)
{
  _Bool well_chunk;
  unsigned long long ptr;
  unsigned long long start;
  unsigned long long size;
  unsigned long long lo_ofs;
  unsigned long long hi_ofs;
  well_chunk = is_well_chunk_bool(chunk$154);
  if (well_chunk) {
    ptr = getMemRegion_block_ptr(mr$150);
    start = getMemRegion_start_addr(mr$150);
    size = getMemRegion_block_size(mr$150);
    lo_ofs = get_subl(addr, start);
    hi_ofs = get_addl(lo_ofs, (unsigned long long) chunk$154);
    if (0LLU <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 18446744073709551615LLU - (unsigned long long) chunk$154
            && 0LLU == lo_ofs % (unsigned long long) chunk$154) {
        return ptr + lo_ofs;
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

unsigned long long check_mem(unsigned long long *l$168, unsigned long long addr$170, unsigned int chunk$172)
{
  struct memory_regions *mrs;
  unsigned long long check_mem_ctx;
  unsigned long long check_mem_stk;
  unsigned long long check_mem_content;
  mrs = eval_mem_regions();
  check_mem_ctx = check_mem_aux((*mrs).bpf_ctx, addr$170, chunk$172);
  if (check_mem_ctx == 0LLU) {
    check_mem_stk = check_mem_aux((*mrs).bpf_stk, addr$170, chunk$172);
    if (check_mem_stk == 0LLU) {
      check_mem_content = check_mem_aux((*mrs).content, addr$170, chunk$172);
      if (check_mem_content == 0LLU) {
        return 0LLU;
      } else {
        return check_mem_content;
      }
    } else {
      return check_mem_stk;
    }
  } else {
    return check_mem_ctx;
  }
}

_Bool comp_and_0x08_byte(unsigned char x$182)
{
  return 0 == (x$182 & 8);
}

void step_opcode_alu64(unsigned long long pc, unsigned int dst, unsigned long long dst64, unsigned long long src64, unsigned char op$192)
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

void step_opcode_alu32(unsigned long long pc$204, unsigned int dst$206, unsigned int dst32, unsigned int src32$210, unsigned char op$212)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$212);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$206, (unsigned long long) (dst32 + src32$210));
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst$206, (unsigned long long) (dst32 - src32$210));
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst$206, (unsigned long long) (dst32 * src32$210));
      upd_flag(0);
      return;
    case 48:
      if (src32$210 != 0U) {
        upd_reg(dst$206, (unsigned long long) (dst32 / src32$210));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$206, (unsigned long long) (dst32 | src32$210));
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst$206, (unsigned long long) (dst32 & src32$210));
      upd_flag(0);
      return;
    case 96:
      if (src32$210 < 32U) {
        upd_reg(dst$206, (unsigned long long) (dst32 << src32$210));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$210 < 32U) {
        upd_reg(dst$206, (unsigned long long) (dst32 >> src32$210));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst$206, (unsigned long long) -dst32);
      upd_flag(0);
      return;
    case 144:
      if (src32$210 != 0U) {
        upd_reg(dst$206, (unsigned long long) (dst32 % src32$210));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$206, (unsigned long long) (dst32 ^ src32$210));
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst$206, src32$210);
      upd_flag(0);
      return;
    case 192:
      if (src32$210 < 32U) {
        upd_reg(dst$206, (unsigned long long) ((int) dst32 >> src32$210));
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

void step_opcode_branch(unsigned long long pc$216, unsigned long long dst64$218, unsigned long long src64$220, unsigned char op$222, unsigned long long ofs)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op$222);
  switch (opcode_jmp) {
    case 0:
      upd_pc(pc$216 + ofs);
      upd_flag(0);
      return;
    case 16:
      if (dst64$218 == src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 32:
      if (dst64$218 > src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 48:
      if (dst64$218 >= src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 64:
      if (dst64$218 < src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 80:
      if (dst64$218 <= src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 96:
      if ((dst64$218 & src64$220) != 0LLU) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 112:
      if (dst64$218 != src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 144:
      if ((long long) dst64$218 > (long long) src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 160:
      if ((long long) dst64$218 >= (long long) src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 176:
      if ((long long) dst64$218 < (long long) src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 192:
      if ((long long) dst64$218 <= (long long) src64$220) {
        upd_pc(pc$216 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 208:
      upd_flag(1);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_imm(unsigned long long pc$228, unsigned int dst$230, unsigned long long dst64$232, unsigned long long imm64, unsigned char op$236, unsigned long long len, unsigned long long *l$240)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  unsigned long long n_imm64;
  opcode_ld = get_opcode_mem_ld_imm(op$236);
  switch (opcode_ld) {
    case 24:
      if (pc$228 + 1LLU < len) {
        next_ins = list_get(l$240, pc$228 + 1LLU);
        next_imm = get_immediate(next_ins);
        n_imm64 = eval_immediate(next_imm);
        upd_reg(dst$230, imm64 | n_imm64 << 32U);
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

void step_opcode_mem_ld_reg(unsigned long long pc$250, unsigned int dst$252, unsigned long long dst64$254, unsigned long long src64$256, unsigned char op$258, unsigned long long ofs64, unsigned long long addr$262, unsigned long long *l$264)
{
  unsigned char opcode_ld$266;
  unsigned long long check_ldxw;
  unsigned long long v_xw;
  unsigned long long check_ldxh;
  unsigned long long v_xh;
  unsigned long long check_ldxb;
  unsigned long long v_xb;
  unsigned long long check_ldxdw;
  unsigned long long v_xdw;
  opcode_ld$266 = get_opcode_mem_ld_reg(op$258);
  switch (opcode_ld$266) {
    case 97:
      check_ldxw = check_mem(l$264, addr$262, 4U);
      if (check_ldxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xw = load_mem(4U, src64$256 + ofs64);
        upd_reg(dst$252, v_xw);
        upd_flag(0);
        return;
      }
    case 105:
      check_ldxh = check_mem(l$264, addr$262, 2U);
      if (check_ldxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xh = load_mem(2U, src64$256 + ofs64);
        upd_reg(dst$252, v_xh);
        upd_flag(0);
        return;
      }
    case 113:
      check_ldxb = check_mem(l$264, addr$262, 1U);
      if (check_ldxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xb = load_mem(1U, src64$256 + ofs64);
        upd_reg(dst$252, v_xb);
        upd_flag(0);
        return;
      }
    case 121:
      check_ldxdw = check_mem(l$264, addr$262, 8U);
      if (check_ldxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xdw = load_mem(8U, src64$256 + ofs64);
        upd_reg(dst$252, v_xdw);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(unsigned long long pc$284, unsigned int dst$286, unsigned long long dst64$288, int imm, unsigned char op$292, unsigned long long ofs64$294, unsigned long long addr$296, unsigned long long *l$298)
{
  unsigned char opcode_st;
  unsigned long long check_stw;
  unsigned long long check_sth;
  unsigned long long check_stb;
  unsigned long long check_stdw;
  opcode_st = get_opcode_mem_st_imm(op$292);
  switch (opcode_st) {
    case 98:
      check_stw = check_mem(l$298, addr$296, 4U);
      if (check_stw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, dst64$288 + ofs64$294, imm);
        upd_flag(0);
        return;
      }
    case 106:
      check_sth = check_mem(l$298, addr$296, 2U);
      if (check_sth == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, dst64$288 + ofs64$294, imm);
        upd_flag(0);
        return;
      }
    case 114:
      check_stb = check_mem(l$298, addr$296, 1U);
      if (check_stb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, dst64$288 + ofs64$294, imm);
        upd_flag(0);
        return;
      }
    case 122:
      check_stdw = check_mem(l$298, addr$296, 8U);
      if (check_stdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, dst64$288 + ofs64$294, imm);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long pc$310, unsigned int dst$312, unsigned long long dst64$314, unsigned long long src64$316, unsigned char op$318, unsigned long long ofs64$320, unsigned long long addr$322, unsigned long long *l$324)
{
  unsigned char opcode_st$326;
  unsigned long long check_stxw;
  unsigned long long check_stxh;
  unsigned long long check_stxb;
  unsigned long long check_stxdw;
  opcode_st$326 = get_opcode_mem_st_reg(op$318);
  switch (opcode_st$326) {
    case 99:
      check_stxw = check_mem(l$324, addr$322, 4U);
      if (check_stxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, dst64$314 + ofs64$320, src64$316);
        upd_flag(0);
        return;
      }
    case 107:
      check_stxh = check_mem(l$324, addr$322, 2U);
      if (check_stxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, dst64$314 + ofs64$320, src64$316);
        upd_flag(0);
        return;
      }
    case 115:
      check_stxb = check_mem(l$324, addr$322, 1U);
      if (check_stxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, dst64$314 + ofs64$320, src64$316);
        upd_flag(0);
        return;
      }
    case 123:
      check_stxdw = check_mem(l$324, addr$322, 8U);
      if (check_stxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, dst64$314 + ofs64$320, src64$316);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(unsigned long long len$336, unsigned long long *l$338)
{
  unsigned long long pc$340;
  unsigned long long ins$342;
  unsigned char op$344;
  unsigned char opc;
  unsigned int dst$348;
  unsigned long long dst64$350;
  _Bool is_imm;
  int imm$354;
  unsigned long long imm64$356;
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
  unsigned long long ofs$382;
  _Bool is_imm$384;
  int imm$386;
  unsigned long long imm64$388;
  unsigned int src$390;
  unsigned long long src64$392;
  unsigned int dst$394;
  unsigned long long dst64$396;
  int imm$398;
  unsigned long long imm64$400;
  unsigned int dst$402;
  unsigned long long dst64$404;
  unsigned int src$406;
  unsigned long long src64$408;
  unsigned long long ofs$410;
  unsigned long long ofs64$412;
  unsigned long long addr$414;
  unsigned int dst$416;
  unsigned long long dst64$418;
  unsigned long long ofs$420;
  unsigned long long ofs64$422;
  int imm$424;
  unsigned long long addr$426;
  unsigned int dst$428;
  unsigned long long dst64$430;
  unsigned int src$432;
  unsigned long long src64$434;
  unsigned long long ofs$436;
  unsigned long long ofs64$438;
  unsigned long long addr$440;
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
        imm64$356 = eval_immediate(imm$354);
        step_opcode_alu64(pc$340, dst$348, dst64$350, imm64$356, op$344);
        return;
      } else {
        src = get_src(ins$342);
        src64$360 = eval_reg(src);
        step_opcode_alu64(pc$340, dst$348, dst64$350, src64$360, op$344);
        return;
      }
    case 4:
      dst$362 = get_dst(ins$342);
      dst64$364 = eval_reg(dst$362);
      dst32$366 = reg64_to_reg32(dst64$364);
      is_imm$368 = comp_and_0x08_byte(op$344);
      if (is_imm$368) {
        imm$370 = get_immediate(ins$342);
        step_opcode_alu32(pc$340, dst$362, dst32$366, imm$370, op$344);
        return;
      } else {
        src$372 = get_src(ins$342);
        src64$374 = eval_reg(src$372);
        src32$376 = reg64_to_reg32(src64$374);
        step_opcode_alu32(pc$340, dst$362, dst32$366, src32$376, op$344);
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
        step_opcode_branch(pc$340, dst64$380, imm64$388, op$344, ofs$382);
        return;
      } else {
        src$390 = get_src(ins$342);
        src64$392 = eval_reg(src$390);
        step_opcode_branch(pc$340, dst64$380, src64$392, op$344, ofs$382);
        return;
      }
    case 0:
      dst$394 = get_dst(ins$342);
      dst64$396 = eval_reg(dst$394);
      imm$398 = get_immediate(ins$342);
      imm64$400 = eval_immediate(imm$398);
      step_opcode_mem_ld_imm(pc$340, dst$394, dst64$396, imm64$400, op$344,
                             len$336, l$338);
      return;
    case 1:
      dst$402 = get_dst(ins$342);
      dst64$404 = eval_reg(dst$402);
      src$406 = get_src(ins$342);
      src64$408 = eval_reg(src$406);
      ofs$410 = get_offset(ins$342);
      ofs64$412 = eval_offset(ofs$410);
      addr$414 = get_addl(src64$408, ofs64$412);
      step_opcode_mem_ld_reg(pc$340, dst$402, dst64$404, src64$408, op$344,
                             ofs64$412, addr$414, l$338);
      return;
    case 2:
      dst$416 = get_dst(ins$342);
      dst64$418 = eval_reg(dst$416);
      ofs$420 = get_offset(ins$342);
      ofs64$422 = eval_offset(ofs$420);
      imm$424 = get_immediate(ins$342);
      addr$426 = get_addl(dst64$418, ofs64$422);
      step_opcode_mem_st_imm(pc$340, dst$416, dst64$418, imm$424, op$344,
                             ofs64$422, addr$426, l$338);
      return;
    case 3:
      dst$428 = get_dst(ins$342);
      dst64$430 = eval_reg(dst$428);
      src$432 = get_src(ins$342);
      src64$434 = eval_reg(src$432);
      ofs$436 = get_offset(ins$342);
      ofs64$438 = eval_offset(ofs$436);
      addr$440 = get_addl(dst64$430, ofs64$438);
      step_opcode_mem_st_reg(pc$340, dst$428, dst64$430, src64$434, op$344,
                             ofs64$438, addr$440, l$338);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned long long len$442, unsigned int fuel, unsigned long long *l$446)
{
  unsigned int fuel$448;
  unsigned long long pc$450;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel$448 = fuel - 1U;
    pc$450 = eval_pc();
    if (pc$450 < len$442) {
      step(len$442, l$446);
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
        bpf_interpreter_aux(len$442, fuel$448, l$446);
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

unsigned long long bpf_interpreter(unsigned long long len$454, unsigned int fuel$456, unsigned long long *l$458)
{
  struct memory_regions *mrs$460;
  int f$462;
  mrs$460 = eval_mem_regions();
  upd_reg(1U, (*(*mrs$460).bpf_ctx).start_addr);
  bpf_interpreter_aux(len$454, fuel$456, l$458);
  f$462 = eval_flag();
  if (f$462 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


