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

unsigned long long eval_pc (void);

void upd_pc(unsigned long long);

void upd_pc_incr(void);

unsigned long long eval_reg(unsigned int);

void upd_reg(unsigned int, unsigned long long);

int eval_flag(void);

void upd_flag(int);

unsigned long long load_mem(unsigned int, unsigned long long);

void store_mem_reg(unsigned int, unsigned long long, unsigned long long);

void store_mem_imm(unsigned int, unsigned long long, int);

//test

unsigned long long list_get(unsigned long long *, unsigned long long);

unsigned char get_opcode(unsigned long long);

unsigned int get_dst(unsigned long long);

unsigned int get_src(unsigned long long);

short get_offset(unsigned long long);

int get_immediate(unsigned long long);

unsigned long long get_addl(unsigned long long, unsigned long long);

unsigned long long getMemRegion_block_ptr(struct $104);

unsigned long long getMemRegion_start_addr(struct $104);

unsigned long long getMemRegion_block_size(struct $104);

struct $104 getMemRegions_bpf_ctx(struct $107);

struct $104 getMemRegions_bpf_stk(struct $107);

struct $104 getMemRegions_content(struct $107);

unsigned long long get_subl(unsigned long long, unsigned long long);

unsigned long long check_mem_aux(struct $104, unsigned long long, unsigned int);

unsigned long long check_mem(struct $107, unsigned long long, unsigned int);

void step(unsigned long long *, unsigned long long, struct $107);

void bpf_interpreter_aux(unsigned long long *, unsigned long long, struct $107, unsigned int);

unsigned long long bpf_interpreter(unsigned long long *, unsigned long long, struct $107, unsigned int);
