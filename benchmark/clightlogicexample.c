#include "clightlogicexample.h"

static void upd_pc_incr(struct bpf_state* st) {
  (*st).state_pc = (*st).state_pc+1;
  return ;
}

static void upd_reg (struct bpf_state* st, unsigned int i, unsigned long long v){
  (*st).regsmap[i] = v;
  return ;
}

static void upd_flag(struct bpf_state* st, int f){
  (*st).bpf_flag = f;
  return ;
}

static struct memory_region *eval_mem_regions(struct bpf_state* st){
  return (*st).mrs;
}


unsigned long long list_get(unsigned long long *l, int idx)
{
  return *(l + idx);
}

struct memory_region *get_mem_region(struct bpf_state* st, unsigned int n)
{
  struct memory_region *mrs;
  mrs = eval_mem_regions(st);
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

unsigned int get_addr_ofs(unsigned long long x, int ofs)
{
  return (unsigned int) (x + (unsigned long long) ofs);
}

static _Bool is_well_chunk_bool(unsigned int chunk)
{
  _Bool b;
  switch (chunk) {
    case 1:
      b = 1;
      break;
    case 2:
      b = 1;
      break;
    case 4:
      b = 1;
      break;
    case 8:
      b = 1;
      break;
    default:
      b = 0;    
  }
  return b;
}

unsigned int calc_sum(unsigned int v, unsigned int n)
{
  unsigned int n1;
  unsigned int nv;
  if (n == 0U) {
    return 0U;
  } else {
    n1 = n - 1U;
    nv = get_add(v, 1U);
    return calc_sum(nv, n1);
  }
}

void rec_upd_pc(struct bpf_state* st, unsigned int n)
{
  unsigned int n1;
  if (n == 0U) {
    return;
  } else {
    n1 = n - 1U;
    upd_pc_incr(st);
    rec_upd_pc(st, n1);
    return;
  }
}

void step_opcode_mem_ld_imm(struct bpf_state* st, int imm, int pc, int len, unsigned int dst, unsigned char op, unsigned long long *l)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  opcode_ld = get_opcode_mem_ld_imm(op);
  switch (opcode_ld) {
    case 24:
      if (pc + 1 < len) {
        next_ins = list_get(l, pc + 1);
        next_imm = get_immediate(next_ins);
        upd_reg(st, dst,
                (unsigned long long) (unsigned int) imm
                  | (unsigned long long) (unsigned int) next_imm << 32U);
        upd_pc_incr(st);
        upd_flag(st, 0);
        return;
      } else {
        upd_flag(st, -5);
        return;
      }
    default:
      upd_flag(st, -1);
      return;
    
  }
}
