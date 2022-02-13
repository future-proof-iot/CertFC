#include "interpreter.h"
#include <stdint.h> /* for uintptr_t */
/*
#include <inttypes.h>
#include<stdlib.h>
#include<stddef.h>

void print_bpf_state(struct bpf_state* st){
  printf("pc= %" PRIu64 "\n", (unsigned long long) (*st).state_pc);
  printf("flag= %d\n", (*st).bpf_flag);
  for(int i = 0; i < 11; i++){
    printf("R%d",i);
    printf("= %" PRIu64 ";", (unsigned long long) (*st).regsmap[i]);
  }
  printf("\n");
}
*/

static __attribute__((always_inline)) inline int eval_pc (struct bpf_state* st) {
  return (*st).state_pc;
}

static __attribute__((always_inline)) inline void upd_pc(struct bpf_state* st, int pc) {
  (*st).state_pc = pc;
  return ;
}
static __attribute__((always_inline)) inline void upd_pc_incr(struct bpf_state* st) {
  (*st).state_pc = (*st).state_pc+1;
  return ;
}


static __attribute__((always_inline)) inline unsigned long long eval_reg(struct bpf_state* st, unsigned int i){
  return (*st).regsmap[i];
}

static __attribute__((always_inline)) inline void upd_reg (struct bpf_state* st, unsigned int i, unsigned long long v){
  (*st).regsmap[i] = v;
  return ;
}

static __attribute__((always_inline)) inline int eval_flag(struct bpf_state* st){
  return (*st).bpf_flag;
}

static __attribute__((always_inline)) inline void upd_flag(struct bpf_state* st, int f){
  (*st).bpf_flag = f;
  return ;
}

static __attribute__((always_inline)) inline unsigned int eval_mrs_num(struct bpf_state* st){
  return (*st).mrs_num;
}

static __attribute__((always_inline)) inline struct memory_region *eval_mrs_regions(struct bpf_state* st){
  return (*st).mrs;
}

/*
void add_mem_region(struct bpf_state* st, struct memory_region* mr){
  (*st).mrs[(*st).mem_num] = *mr;
  (*st).mem_num += 1;
  return ;
}

void add_mem_region_ctx(struct bpf_state* st, struct memory_region* mr){
  (*st).mrs[0] = *mr;
  (*st).mem_num = 1;
  return ;
} */

static __attribute__((always_inline)) inline unsigned long long load_mem(struct bpf_state* st, unsigned int chunk, unsigned char* addr){
  /*if (addr == 0U) {
    (*st).bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
  else{*/
    switch (chunk) {
      case 1: return *(unsigned char *) addr;
      case 2: return *(unsigned short *) addr;
      case 4: return *(unsigned int *) addr;
      case 8: return *(unsigned long long *) addr;
      default: /*printf ("load:addr = %" PRIu64 "\n", v); (*st).bpf_flag = BPF_ILLEGAL_MEM;*/ return 0LLU;
    }
  //}
}

static __attribute__((always_inline)) inline void store_mem_reg(struct bpf_state* st, unsigned int chunk, unsigned char* addr, unsigned long long v){
  /*if (addr == 0U) {
    (*st).bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
  else{*/
    switch (chunk) {
      case 1: *(unsigned char *) addr = v; return ;
      case 2: *(unsigned short *) addr = v; return ;
      case 4: *(unsigned int *) addr = v; return ;
      case 8: *(unsigned long long *) addr = v; return ;
      default: /*printf ("store_reg:addr = %" PRIu64 "\n", addr); (*st).bpf_flag = BPF_ILLEGAL_MEM;*/ return ;
    }
  //}
}

static __attribute__((always_inline)) inline void store_mem_imm(struct bpf_state* st, unsigned int chunk, unsigned char* addr, int v){
  /*if (addr == 0U) {
    (*st).bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
  else{*/
    switch (chunk) {
      case 1: *(unsigned char *) addr = v; return ;
      case 2: *(unsigned short *) addr = v; return ;
      case 4: *(unsigned int *) addr = v; return ;
      case 8: *(unsigned long long *) addr = v; return ;
      default: /*printf ("store_imm:addr = %" PRIu64 "\n", addr); (*st).bpf_flag = BPF_ILLEGAL_MEM;*/ return ;
    }
  //}
}

static __attribute__((always_inline)) inline int eval_ins_len(struct bpf_state* st)
{
  return (*st).ins_len;
}

static __attribute__((always_inline)) inline unsigned long long eval_ins(struct bpf_state* st, int idx)
{
  return *((*st).ins + idx);
}

static __attribute__((always_inline)) inline _Bool cmp_ptr32_nullM(struct bpf_state* st, unsigned char* addr){
   return (addr == 0);
}
/*******************below code are automatically generated by dx (after repatch) ***************************/
