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

extern unsigned char get_opcode_alu64_imm(unsigned long long);

extern unsigned char get_opcode_alu64_reg(unsigned long long);

extern unsigned char get_opcode_alu32_imm(unsigned long long);

extern unsigned char get_opcode_alu32_reg(unsigned long long);

extern unsigned char get_opcode_branch_imm(unsigned long long);

extern unsigned char get_opcode_branch_reg(unsigned long long);

extern unsigned char get_opcode_mem_ld_imm(unsigned long long);

extern unsigned char get_opcode_mem_ld_reg(unsigned long long);

extern unsigned char get_opcode_mem_st_imm(unsigned long long);

extern unsigned char get_opcode_mem_st_reg(unsigned long long);

extern unsigned char get_opcode(unsigned long long);

extern unsigned long long get_addl(unsigned long long, unsigned long long);

extern unsigned long long get_subl(unsigned long long, unsigned long long);

extern unsigned long long getMemRegion_block_ptr(struct memory_region *);

extern unsigned long long getMemRegion_start_addr(struct memory_region *);

extern unsigned long long getMemRegion_block_size(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned long long check_mem_aux(struct memory_region *, unsigned long long, unsigned int);

extern unsigned long long check_mem(unsigned long long *, unsigned long long, unsigned int);

extern void step_opcode_alu64_imm(unsigned long long *);

extern void step_opcode_alu64_reg(unsigned long long *);

extern void step_opcode_alu32_imm(unsigned long long *);

extern void step_opcode_alu32_reg(unsigned long long *);

extern void step_opcode_branch_imm(unsigned long long *);

extern void step_opcode_branch_reg(unsigned long long *);

extern void step_opcode_mem_ld_imm(unsigned long long *, unsigned long long);

extern void step_opcode_mem_ld_reg(unsigned long long *);

extern void step_opcode_mem_st_imm(unsigned long long *);

extern void step_opcode_mem_st_reg(unsigned long long *);

extern void step(unsigned long long *, unsigned long long);

extern void bpf_interpreter_aux(unsigned long long *, unsigned long long, unsigned int);

extern unsigned long long bpf_interpreter(unsigned long long *, unsigned long long, unsigned int);

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

unsigned long long list_get(unsigned long long *l, unsigned long long idx0)
{
  return *(l + idx0);
}

unsigned int get_dst(unsigned long long ins1)
{
  return (unsigned int) ((ins1 & 4095LLU) >> 8LLU);
}

unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

unsigned int get_src(unsigned long long ins2)
{
  return (unsigned int) ((ins2 & 65535LLU) >> 12LLU);
}

unsigned long long get_offset(unsigned long long i)
{
  return i << 32LLU >> 48LLU;
}

unsigned long long eval_offset(unsigned long long i$118)
{
  return i$118;
}

int get_immediate(unsigned long long i1)
{
  return (int) (i1 >> 32LLU);
}

unsigned long long eval_immediate(int i$122)
{
  return (unsigned long long) i$122;
}

unsigned char get_opcode_alu64_imm(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_alu64_reg(unsigned long long ins$126)
{
  return (unsigned char) (ins$126 & 255LLU);
}

unsigned char get_opcode_alu32_imm(unsigned long long ins$128)
{
  return (unsigned char) (ins$128 & 255LLU);
}

unsigned char get_opcode_alu32_reg(unsigned long long ins$130)
{
  return (unsigned char) (ins$130 & 255LLU);
}

unsigned char get_opcode_branch_imm(unsigned long long ins$132)
{
  return (unsigned char) (ins$132 & 255LLU);
}

unsigned char get_opcode_branch_reg(unsigned long long ins$134)
{
  return (unsigned char) (ins$134 & 255LLU);
}

unsigned char get_opcode_mem_ld_imm(unsigned long long ins$136)
{
  return (unsigned char) (ins$136 & 255LLU);
}

unsigned char get_opcode_mem_ld_reg(unsigned long long ins$138)
{
  return (unsigned char) (ins$138 & 255LLU);
}

unsigned char get_opcode_mem_st_imm(unsigned long long ins$140)
{
  return (unsigned char) (ins$140 & 255LLU);
}

unsigned char get_opcode_mem_st_reg(unsigned long long ins$142)
{
  return (unsigned char) (ins$142 & 255LLU);
}

unsigned char get_opcode(unsigned long long ins$144)
{
  return (unsigned char) (ins$144 & 15LLU);
}

unsigned long long get_addl(unsigned long long x, unsigned long long y)
{
  return x + y;
}

unsigned long long get_subl(unsigned long long x1, unsigned long long y1)
{
  return x1 - y1;
}

unsigned long long getMemRegion_block_ptr(struct memory_region *mr0)
{
  return 1LLU;
}

unsigned long long getMemRegion_start_addr(struct memory_region *mr1)
{
  return (*mr1).start_addr;
}

unsigned long long getMemRegion_block_size(struct memory_region *mr2)
{
  return (*mr2).block_size;
}

_Bool is_well_chunk_bool(unsigned int chunk0)
{
  switch (chunk0) {
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

unsigned long long check_mem_aux(struct memory_region *mr3, unsigned long long addr0, unsigned int chunk1)
{
  _Bool well_chunk;
  unsigned long long ptr;
  unsigned long long start;
  unsigned long long size;
  unsigned long long lo_ofs;
  unsigned long long hi_ofs;
  well_chunk = is_well_chunk_bool(chunk1);
  if (well_chunk) {
    ptr = getMemRegion_block_ptr(mr3);
    start = getMemRegion_start_addr(mr3);
    size = getMemRegion_block_size(mr3);
    lo_ofs = get_subl(addr0, start);
    hi_ofs = get_addl(lo_ofs, (unsigned long long) chunk1);
    if (0LLU <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 18446744073709551615LLU - (unsigned long long) chunk1
            && 0LLU == lo_ofs % (unsigned long long) chunk1) {
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

unsigned long long check_mem(unsigned long long *l$180, unsigned long long addr1, unsigned int chunk2)
{
  struct memory_regions *mrs;
  unsigned long long check_mem_ctx;
  unsigned long long check_mem_stk;
  unsigned long long check_mem_content;
  mrs = eval_mem_regions();
  check_mem_ctx = check_mem_aux((*mrs).bpf_ctx, addr1, chunk2);
  if (check_mem_ctx == 0LLU) {
    check_mem_stk = check_mem_aux((*mrs).bpf_stk, addr1, chunk2);
    if (check_mem_stk == 0LLU) {
      check_mem_content = check_mem_aux((*mrs).content, addr1, chunk2);
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

void step_opcode_alu64_imm(unsigned long long *l$194)
{
  unsigned long long pc;
  unsigned long long ins$198;
  unsigned int dst;
  unsigned long long dst64;
  int imm;
  unsigned long long imm64;
  unsigned char opcode;
  pc = eval_pc();
  ins$198 = list_get(l$194, pc);
  dst = get_dst(ins$198);
  dst64 = eval_reg(dst);
  imm = get_immediate(ins$198);
  imm64 = eval_immediate(imm);
  opcode = get_opcode_alu64_imm(ins$198);
  switch (opcode) {
    case 7:
      upd_reg(dst, dst64 + imm64);
      upd_flag(0);
      return;
    case 23:
      upd_reg(dst, dst64 - imm64);
      upd_flag(0);
      return;
    case 39:
      upd_reg(dst, dst64 * imm64);
      upd_flag(0);
      return;
    case 55:
      if (imm64 != 0LLU) {
        upd_reg(dst, dst64 / imm64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 71:
      upd_reg(dst, dst64 | imm64);
      upd_flag(0);
      return;
    case 87:
      upd_reg(dst, dst64 & imm64);
      upd_flag(0);
      return;
    case 103:
      if (imm64 < 64LLU) {
        upd_reg(dst, dst64 << imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 119:
      if (imm64 < 64LLU) {
        upd_reg(dst, dst64 >> imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 135:
      upd_reg(dst, -dst64);
      upd_flag(0);
      return;
    case 151:
      if (imm64 != 0LLU) {
        upd_reg(dst, dst64 % imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 167:
      upd_reg(dst, dst64 ^ imm64);
      upd_flag(0);
      return;
    case 183:
      upd_reg(dst, imm64);
      upd_flag(0);
      return;
    case 199:
      if (imm64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> imm);
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

void step_opcode_alu64_reg(unsigned long long *l$210)
{
  unsigned long long pc$212;
  unsigned long long ins$214;
  unsigned int dst$216;
  unsigned long long dst64$218;
  unsigned int src;
  unsigned long long src64;
  unsigned char opcode$224;
  unsigned int src32;
  unsigned int src32$228;
  unsigned int src32$230;
  unsigned int src32$232;
  pc$212 = eval_pc();
  ins$214 = list_get(l$210, pc$212);
  dst$216 = get_dst(ins$214);
  dst64$218 = eval_reg(dst$216);
  src = get_src(ins$214);
  src64 = eval_reg(src);
  opcode$224 = get_opcode_alu64_reg(ins$214);
  switch (opcode$224) {
    case 15:
      upd_reg(dst$216, dst64$218 + src64);
      upd_flag(0);
      return;
    case 31:
      upd_reg(dst$216, dst64$218 - src64);
      upd_flag(0);
      return;
    case 47:
      upd_reg(dst$216, dst64$218 * src64);
      upd_flag(0);
      return;
    case 63:
      if (src64 != 0LLU) {
        upd_reg(dst$216, dst64$218 / src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 79:
      upd_reg(dst$216, dst64$218 | src64);
      upd_flag(0);
      return;
    case 95:
      upd_reg(dst$216, dst64$218 & src64);
      upd_flag(0);
      return;
    case 111:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst$216, dst64$218 << src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 127:
      src32$228 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst$216, dst64$218 >> src32$228);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 159:
      src32$230 = reg64_to_reg32(src64);
      if (src64 != 0LLU) {
        upd_reg(dst$216, dst64$218 % src32$230);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 175:
      upd_reg(dst$216, dst64$218 ^ src64);
      upd_flag(0);
      return;
    case 191:
      upd_reg(dst$216, src64);
      upd_flag(0);
      return;
    case 207:
      src32$232 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst$216, (long long) dst64$218 >> src32$232);
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

void step_opcode_alu32_imm(unsigned long long *l$234)
{
  unsigned long long pc$236;
  unsigned long long ins$238;
  unsigned int dst$240;
  unsigned long long dst64$242;
  unsigned int dst32;
  int imm$246;
  unsigned char opcode$248;
  pc$236 = eval_pc();
  ins$238 = list_get(l$234, pc$236);
  dst$240 = get_dst(ins$238);
  dst64$242 = eval_reg(dst$240);
  dst32 = reg64_to_reg32(dst64$242);
  imm$246 = get_immediate(ins$238);
  opcode$248 = get_opcode_alu32_imm(ins$238);
  switch (opcode$248) {
    case 4:
      upd_reg(dst$240, (unsigned long long) (dst32 + imm$246));
      upd_flag(0);
      return;
    case 20:
      upd_reg(dst$240, (unsigned long long) (dst32 - imm$246));
      upd_flag(0);
      return;
    case 36:
      upd_reg(dst$240, (unsigned long long) (dst32 * imm$246));
      upd_flag(0);
      return;
    case 52:
      if (imm$246 != 0U) {
        upd_reg(dst$240, (unsigned long long) (dst32 / imm$246));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 68:
      upd_reg(dst$240, (unsigned long long) (dst32 | imm$246));
      upd_flag(0);
      return;
    case 84:
      upd_reg(dst$240, (unsigned long long) (dst32 & imm$246));
      upd_flag(0);
      return;
    case 100:
      if (imm$246 < 32U) {
        upd_reg(dst$240, (unsigned long long) (dst32 << imm$246));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 116:
      if (imm$246 < 32U) {
        upd_reg(dst$240, (unsigned long long) (dst32 >> imm$246));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 132:
      upd_reg(dst$240, (unsigned long long) -dst32);
      upd_flag(0);
      return;
    case 148:
      if (imm$246 != 0U) {
        upd_reg(dst$240, (unsigned long long) (dst32 % imm$246));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 164:
      upd_reg(dst$240, (unsigned long long) (dst32 ^ imm$246));
      upd_flag(0);
      return;
    case 180:
      upd_reg(dst$240, imm$246);
      upd_flag(0);
      return;
    case 196:
      if (imm$246 < 32U) {
        upd_reg(dst$240, (unsigned long long) ((int) dst32 >> imm$246));
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

void step_opcode_alu32_reg(unsigned long long *l$250)
{
  unsigned long long pc$252;
  unsigned long long ins$254;
  unsigned int dst$256;
  unsigned long long dst64$258;
  unsigned int dst32$260;
  unsigned int src$262;
  unsigned long long src64$264;
  unsigned int src32$266;
  unsigned char opcode$268;
  pc$252 = eval_pc();
  ins$254 = list_get(l$250, pc$252);
  dst$256 = get_dst(ins$254);
  dst64$258 = eval_reg(dst$256);
  dst32$260 = reg64_to_reg32(dst64$258);
  src$262 = get_src(ins$254);
  src64$264 = eval_reg(src$262);
  src32$266 = reg64_to_reg32(src64$264);
  opcode$268 = get_opcode_alu32_reg(ins$254);
  switch (opcode$268) {
    case 12:
      upd_reg(dst$256, (unsigned long long) (dst32$260 + src32$266));
      upd_flag(0);
      return;
    case 28:
      upd_reg(dst$256, (unsigned long long) (dst32$260 - src32$266));
      upd_flag(0);
      return;
    case 44:
      upd_reg(dst$256, (unsigned long long) (dst32$260 * src32$266));
      upd_flag(0);
      return;
    case 60:
      if (src32$266 != 0U) {
        upd_reg(dst$256, (unsigned long long) (dst32$260 / src32$266));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 76:
      upd_reg(dst$256, (unsigned long long) (dst32$260 | src32$266));
      upd_flag(0);
      return;
    case 92:
      upd_reg(dst$256, (unsigned long long) (dst32$260 & src32$266));
      upd_flag(0);
      return;
    case 108:
      if (src32$266 < 32U) {
        upd_reg(dst$256, (unsigned long long) (dst32$260 << src32$266));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 124:
      if (src32$266 < 32U) {
        upd_reg(dst$256, (unsigned long long) (dst32$260 >> src32$266));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 156:
      if (src32$266 != 0U) {
        upd_reg(dst$256, (unsigned long long) (dst32$260 % src32$266));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 172:
      upd_reg(dst$256, (unsigned long long) (dst32$260 ^ src32$266));
      upd_flag(0);
      return;
    case 188:
      upd_reg(dst$256, src32$266);
      upd_flag(0);
      return;
    case 204:
      if (src32$266 < 32U) {
        upd_reg(dst$256, (unsigned long long) ((int) dst32$260 >> src32$266));
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

void step_opcode_branch_imm(unsigned long long *l$270)
{
  unsigned long long pc$272;
  unsigned long long ins$274;
  unsigned int dst$276;
  unsigned long long dst64$278;
  unsigned long long ofs;
  int imm$282;
  unsigned char opcode$284;
  pc$272 = eval_pc();
  ins$274 = list_get(l$270, pc$272);
  dst$276 = get_dst(ins$274);
  dst64$278 = eval_reg(dst$276);
  ofs = get_offset(ins$274);
  imm$282 = get_immediate(ins$274);
  opcode$284 = get_opcode_branch_imm(ins$274);
  switch (opcode$284) {
    case 5:
      upd_pc(pc$272 + ofs);
      upd_flag(0);
      return;
    case 21:
      if (dst64$278 == (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 37:
      if (dst64$278 > (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 53:
      if (dst64$278 >= (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 69:
      if (dst64$278 < (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 85:
      if (dst64$278 <= (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 101:
      if ((dst64$278 & (unsigned long long) imm$282) != 0LLU) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 117:
      if (dst64$278 != (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 149:
      if ((long long) dst64$278 > (long long) (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 165:
      if ((long long) dst64$278 >= (long long) (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 181:
      if ((long long) dst64$278 < (long long) (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 197:
      if ((long long) dst64$278 <= (long long) (unsigned long long) imm$282) {
        upd_pc(pc$272 + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 213:
      upd_flag(1);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_branch_reg(unsigned long long *l$286)
{
  unsigned long long pc$288;
  unsigned long long ins$290;
  unsigned int dst$292;
  unsigned long long dst64$294;
  unsigned int src$296;
  unsigned long long src64$298;
  unsigned long long ofs$300;
  unsigned char opcode$302;
  pc$288 = eval_pc();
  ins$290 = list_get(l$286, pc$288);
  dst$292 = get_dst(ins$290);
  dst64$294 = eval_reg(dst$292);
  src$296 = get_src(ins$290);
  src64$298 = eval_reg(src$296);
  ofs$300 = get_offset(ins$290);
  opcode$302 = get_opcode_branch_reg(ins$290);
  switch (opcode$302) {
    case 29:
      if (dst64$294 == src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 45:
      if (dst64$294 > src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 61:
      if (dst64$294 >= src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 173:
      if (dst64$294 < src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 189:
      if (dst64$294 <= src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 77:
      if ((dst64$294 & src64$298) != 0LLU) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 93:
      if (dst64$294 != src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 109:
      if ((long long) dst64$294 > (long long) src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 125:
      if ((long long) dst64$294 >= (long long) src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 205:
      if ((long long) dst64$294 < (long long) src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 221:
      if ((long long) dst64$294 <= (long long) src64$298) {
        upd_pc(pc$288 + ofs$300);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_imm(unsigned long long *l$304, unsigned long long len)
{
  unsigned long long pc$308;
  unsigned long long ins$310;
  unsigned int dst$312;
  int imm$314;
  unsigned long long imm64$316;
  unsigned char opcode$318;
  unsigned long long next_ins;
  int next_imm;
  unsigned long long n_imm64;
  pc$308 = eval_pc();
  ins$310 = list_get(l$304, pc$308);
  dst$312 = get_dst(ins$310);
  eval_reg(dst$312);
  get_offset(ins$310);
  imm$314 = get_immediate(ins$310);
  imm64$316 = eval_immediate(imm$314);
  opcode$318 = get_opcode_mem_ld_imm(ins$310);
  switch (opcode$318) {
    case 24:
      if (pc$308 + 1LLU < len) {
        next_ins = list_get(l$304, pc$308 + 1LLU);
        next_imm = get_immediate(next_ins);
        n_imm64 = eval_immediate(next_imm);
        upd_reg(dst$312, imm64$316 | n_imm64 << 32U);
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

void step_opcode_mem_ld_reg(unsigned long long *l$326)
{
  unsigned long long pc$328;
  unsigned long long ins$330;
  unsigned int dst$332;
  unsigned int src$334;
  unsigned long long src64$336;
  unsigned long long ofs$338;
  unsigned long long ofs64;
  unsigned char opcode$342;
  unsigned long long addr_src;
  unsigned long long check_ldxw;
  unsigned long long v_xw;
  unsigned long long check_ldxh;
  unsigned long long v_xh;
  unsigned long long check_ldxb;
  unsigned long long v_xb;
  unsigned long long check_ldxdw;
  unsigned long long v_xdw;
  pc$328 = eval_pc();
  ins$330 = list_get(l$326, pc$328);
  dst$332 = get_dst(ins$330);
  src$334 = get_src(ins$330);
  src64$336 = eval_reg(src$334);
  ofs$338 = get_offset(ins$330);
  ofs64 = eval_offset(ofs$338);
  opcode$342 = get_opcode_mem_ld_reg(ins$330);
  addr_src = get_addl(src64$336, ofs64);
  switch (opcode$342) {
    case 97:
      check_ldxw = check_mem(l$326, addr_src, 4U);
      if (check_ldxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xw = load_mem(4U, src64$336 + ofs64);
        upd_reg(dst$332, v_xw);
        upd_flag(0);
        return;
      }
    case 105:
      check_ldxh = check_mem(l$326, addr_src, 2U);
      if (check_ldxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xh = load_mem(2U, src64$336 + ofs64);
        upd_reg(dst$332, v_xh);
        upd_flag(0);
        return;
      }
    case 113:
      check_ldxb = check_mem(l$326, addr_src, 1U);
      if (check_ldxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xb = load_mem(1U, src64$336 + ofs64);
        upd_reg(dst$332, v_xb);
        upd_flag(0);
        return;
      }
    case 121:
      check_ldxdw = check_mem(l$326, addr_src, 8U);
      if (check_ldxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xdw = load_mem(8U, src64$336 + ofs64);
        upd_reg(dst$332, v_xdw);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(unsigned long long *l$362)
{
  unsigned long long pc$364;
  unsigned long long ins$366;
  unsigned int dst$368;
  unsigned long long dst64$370;
  unsigned long long ofs$372;
  unsigned long long ofs64$374;
  int imm$376;
  unsigned long long addr_dst;
  unsigned char opcode$380;
  unsigned long long check_stw;
  unsigned long long check_sth;
  unsigned long long check_stb;
  unsigned long long check_stdw;
  pc$364 = eval_pc();
  ins$366 = list_get(l$362, pc$364);
  dst$368 = get_dst(ins$366);
  dst64$370 = eval_reg(dst$368);
  ofs$372 = get_offset(ins$366);
  ofs64$374 = eval_offset(ofs$372);
  imm$376 = get_immediate(ins$366);
  addr_dst = get_addl(dst64$370, ofs64$374);
  opcode$380 = get_opcode_mem_st_imm(ins$366);
  switch (opcode$380) {
    case 98:
      check_stw = check_mem(l$362, addr_dst, 4U);
      if (check_stw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, dst64$370 + ofs64$374, imm$376);
        upd_flag(0);
        return;
      }
    case 106:
      check_sth = check_mem(l$362, addr_dst, 2U);
      if (check_sth == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, dst64$370 + ofs64$374, imm$376);
        upd_flag(0);
        return;
      }
    case 114:
      check_stb = check_mem(l$362, addr_dst, 1U);
      if (check_stb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, dst64$370 + ofs64$374, imm$376);
        upd_flag(0);
        return;
      }
    case 122:
      check_stdw = check_mem(l$362, addr_dst, 8U);
      if (check_stdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, dst64$370 + ofs64$374, imm$376);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long *l$390)
{
  unsigned long long pc$392;
  unsigned long long ins$394;
  unsigned int dst$396;
  unsigned long long dst64$398;
  unsigned int src$400;
  unsigned long long src64$402;
  unsigned long long ofs$404;
  unsigned long long ofs64$406;
  unsigned long long addr_dst$408;
  unsigned char opcode$410;
  unsigned long long check_stxw;
  unsigned long long check_stxh;
  unsigned long long check_stxb;
  unsigned long long check_stxdw;
  pc$392 = eval_pc();
  ins$394 = list_get(l$390, pc$392);
  dst$396 = get_dst(ins$394);
  dst64$398 = eval_reg(dst$396);
  src$400 = get_src(ins$394);
  src64$402 = eval_reg(src$400);
  ofs$404 = get_offset(ins$394);
  ofs64$406 = eval_offset(ofs$404);
  addr_dst$408 = get_addl(dst64$398, ofs64$406);
  opcode$410 = get_opcode_mem_st_reg(ins$394);
  switch (opcode$410) {
    case 99:
      check_stxw = check_mem(l$390, addr_dst$408, 4U);
      if (check_stxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, dst64$398 + ofs64$406, src64$402);
        upd_flag(0);
        return;
      }
    case 107:
      check_stxh = check_mem(l$390, addr_dst$408, 2U);
      if (check_stxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, dst64$398 + ofs64$406, src64$402);
        upd_flag(0);
        return;
      }
    case 115:
      check_stxb = check_mem(l$390, addr_dst$408, 1U);
      if (check_stxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, dst64$398 + ofs64$406, src64$402);
        upd_flag(0);
        return;
      }
    case 123:
      check_stxdw = check_mem(l$390, addr_dst$408, 8U);
      if (check_stxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, dst64$398 + ofs64$406, src64$402);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(unsigned long long *l$420, unsigned long long len$422)
{
  unsigned long long pc$424;
  unsigned long long ins$426;
  unsigned char op;
  pc$424 = eval_pc();
  ins$426 = list_get(l$420, pc$424);
  op = get_opcode(ins$426);
  switch (op) {
    case 7:
      step_opcode_alu64_imm(l$420);
      return;
    case 15:
      step_opcode_alu64_reg(l$420);
      return;
    case 4:
      step_opcode_alu32_imm(l$420);
      return;
    case 12:
      step_opcode_alu32_reg(l$420);
      return;
    case 5:
      step_opcode_branch_imm(l$420);
      return;
    case 13:
      step_opcode_branch_reg(l$420);
      return;
    case 8:
      step_opcode_mem_ld_imm(l$420, len$422);
      return;
    case 1:
      step_opcode_mem_ld_reg(l$420);
      return;
    case 9:
      step_opcode_mem_ld_reg(l$420);
      return;
    case 2:
      step_opcode_mem_st_imm(l$420);
      return;
    case 10:
      step_opcode_mem_st_imm(l$420);
      return;
    case 3:
      step_opcode_mem_st_reg(l$420);
      return;
    case 11:
      step_opcode_mem_st_reg(l$420);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned long long *l$430, unsigned long long len$432, unsigned int fuel)
{
  unsigned int fuel$436;
  unsigned long long pc$438;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel$436 = fuel - 1U;
    pc$438 = eval_pc();
    if (pc$438 < len$432) {
      step(l$430, len$432);
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
        bpf_interpreter_aux(l$430, len$432, fuel$436);
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

unsigned long long bpf_interpreter(unsigned long long *l$442, unsigned long long len$444, unsigned int fuel$446)
{
  struct memory_regions *mrs$448;
  int f$450;
  mrs$448 = eval_mem_regions();
  upd_reg(1U, (*(*mrs$448).bpf_ctx).start_addr);
  bpf_interpreter_aux(l$442, len$444, fuel$446);
  f$450 = eval_flag();
  if (f$450 == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


