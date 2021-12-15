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
  unsigned long long regsmap[11];
  struct memory_region *mrs$757165;
  unsigned int $11884978998701;
};

extern unsigned long long list_get(unsigned long long *, int);

extern struct memory_region *get_mem_region(unsigned int);

extern int get_immediate(unsigned long long);

extern unsigned char get_opcode_mem_ld_imm(unsigned char);

extern unsigned int get_add(unsigned int, unsigned int);

extern unsigned int get_addr_ofs(unsigned long long, int);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned int calc_sum(unsigned int, unsigned int);

extern void rec_upd_pc(unsigned int);

extern void step_opcode_mem_ld_imm(int, int, int, unsigned int, unsigned char, unsigned long long *);

extern void upd_pc_incr(void);

extern void upd_reg(unsigned int, unsigned long long);

extern void upd_flag(int);

extern struct memory_region *eval_mem_regions(void);

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

int get_immediate(unsigned long long ins)
{
  return (int) (ins >> 32LLU);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned int get_add(unsigned int x, unsigned int y)
{
  return x + y;
}

unsigned int get_addr_ofs(unsigned long long x$46, int ofs)
{
  return (unsigned int) (x$46 + (unsigned long long) (unsigned int) ofs);
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

unsigned int calc_sum(unsigned int v, unsigned int n$54)
{
  unsigned int n1;
  unsigned int nv;
  if (n$54 == 0U) {
    return 0U;
  } else {
    n1 = n$54 - 1U;
    nv = get_add(v, 1U);
    return calc_sum(nv, n1);
  }
}

void rec_upd_pc(unsigned int n$60)
{
  unsigned int n1$62;
  if (n$60 == 0U) {
    return;
  } else {
    n1$62 = n$60 - 1U;
    upd_pc_incr();
    rec_upd_pc(n1$62);
    return;
  }
}

void step_opcode_mem_ld_imm(int imm, int pc, int len, unsigned int dst, unsigned char op$72, unsigned long long *l$74)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  opcode_ld = get_opcode_mem_ld_imm(op$72);
  switch (opcode_ld) {
    case 24:
      if (pc + 1 < len) {
        next_ins = list_get(l$74, pc + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(dst,
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


