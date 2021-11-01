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

struct $1004 {
  unsigned long long $1005;
  unsigned long long $1006;
};
/*
struct memory_region {
  unsigned long long start_addr;
  unsigned long long block_size;
};
 */

struct $1007 {
  struct $1004 $1008;
  struct $1004 $1009;
  struct $1004 $1010;
};

struct $1007 memory_regions;

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

/*******************automatically generated by dx ***************************/

extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned char get_opcode(unsigned long long);

extern unsigned int get_dst(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern short get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern unsigned long long get_addl(unsigned long long, unsigned long long);

extern unsigned long long get_subl(unsigned long long, unsigned long long);

extern unsigned long long getMemRegion_block_ptr(struct $1004);

extern unsigned long long getMemRegion_start_addr(struct $1004);

extern unsigned long long getMemRegion_block_size(struct $1004);

extern unsigned long long check_mem_aux(struct $1004, unsigned long long, unsigned int);

extern unsigned long long check_mem(unsigned long long, unsigned int);

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

extern struct $1007 eval_mem_regions(void);

extern void upd_mem_regions(struct $1007);

extern unsigned long long load_mem(unsigned int, unsigned long long);

extern void store_mem_imm(unsigned int, unsigned long long, int);

extern void store_mem_reg(unsigned int, unsigned long long, unsigned long long);