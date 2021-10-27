#include<stdio.h>

/*
defining bpf_flag
 */

enum {
    BPF_SUCC_RETURN         = 1,
    BPF_OK = 0,
    BPF_ILLEGAL_INSTRUCTION = -1,
    BPF_ILLEGAL_MEM         = -2,
    BPF_ILLEGAL_JUMP        = -3,
    BPF_ILLEGAL_CALL        = -4,
    BPF_ILLEGAL_LEN         = -5,
    BPF_ILLEGAL_REGISTER    = -6,
    BPF_NO_RETURN           = -7,
    BPF_OUT_OF_BRANCHES     = -8,
    BPF_ILLEGAL_DIV         = -9,
};

int bpf_flag;

struct $104 {
  unsigned long long $105;
  unsigned long long $106;
};
/*
struct memory_region {
  unsigned long long start_addr;
  unsigned long long block_size;
};
 */

struct $107 {
  struct $104 $108;
  struct $104 $109;
  struct $104 $110;
};

/*
struct memory_regions {
  struct memory_region bpf_ctx;
  struct memory_region bpf_stk;
  struct memory_region content;
};   
 */

/*
state:
unsigned long long state_pc;
Unsigned long long regsmap[11];
 */

unsigned long long state_pc;
unsigned long long regsmap[11];

unsigned long long eval_pc () {
  return state_pc;
}


void upd_pc(unsigned long long pc) {
  state_pc = pc;
  return ;
}

unsigned long long eval_reg(unsigned int i){
  if (i < 11){
    return regsmap[i];
  }
  else {
    bpf_flag = BPF_ILLEGAL_REGISTER;
    return 0; //if here we update the bpf_flag, we must check bpf_flag after eval_reg
  }
}

void upd_reg(unsigned int i, unsigned long long v){
  if (i < 11) {
      regsmap[i] = v; //here
  }
  else {
      bpf_flag = BPF_ILLEGAL_REGISTER;
  }
  return ;
}

int eval_flag(){
  return bpf_flag;
}

void upd_flag(int f){
  bpf_flag = f;
  return ;
}

unsigned long long load_mem(unsigned int chunk, unsigned long long v){
  switch (chunk) {
    case 1: return *(unsigned char *) v;
    case 2: return *(unsigned short *) v;
    case 4: return *(unsigned int *) v;
    case 8: return *(unsigned long long *) v;
    default: bpf_flag = BPF_ILLEGAL_MEM; return 0;
  }
}

void store_mem_reg(unsigned int chunk, unsigned long long addr, unsigned long long v){
  switch (chunk) {
    case 1: *(unsigned char *) addr = v; return ;
    case 2: *(unsigned short *) addr = v; return ;
    case 4: *(unsigned int *) addr = v; return ;
    case 8: *(unsigned long long *) addr = v; return ;
    default: bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
}

void store_mem_imm(unsigned int chunk, unsigned long long addr, int v){
  switch (chunk) {
    case 1: *(unsigned char *) addr = v; return ;
    case 2: *(unsigned short *) addr = v; return ;
    case 4: *(unsigned int *) addr = v; return ;
    case 8: *(unsigned long long *) addr = v; return ;
    default: bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
}

extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned char get_opcode(unsigned long long);

extern unsigned int get_dst(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern short get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern unsigned long long get_addl(unsigned long long, unsigned long long);

extern unsigned long long getMemRegion_block_ptr(struct $104);

extern unsigned long long getMemRegion_start_addr(struct $104);

extern unsigned long long getMemRegion_block_size(struct $104);

extern struct $104 getMemRegions_bpf_ctx(struct $107);

extern struct $104 getMemRegions_bpf_stk(struct $107);

extern struct $104 getMemRegions_content(struct $107);

extern unsigned long long get_subl(unsigned long long, unsigned long long);

extern unsigned long long check_mem_aux(struct $104, unsigned long long, unsigned int);

extern unsigned long long check_mem(struct $107, unsigned long long, unsigned int);

extern void step(unsigned long long *, unsigned long long, struct $107);
