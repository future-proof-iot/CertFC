#include<stdio.h>

/*                                                                              
defining bpf_flag                                                               
 */

enum {
    BPF_SUCC_RETURN         = 1,
    BPF_OK                  = 0,
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

struct memory_region {
  unsigned long long start_addr;
  unsigned long long block_size;
  unsigned long long block_ptr_id;
};

struct memory_regions {
  struct memory_region* bpf_ctx;
  struct memory_region* bpf_stk;
  struct memory_region* content;
};

struct bpf_state {
  unsigned long long state_pc;
  unsigned long long regsmap[11];
  int bpf_flag;
  struct memory_regions *mrs;
};


unsigned long long bpf_interpreter(unsigned long long *, unsigned long long, unsigned int, struct bpf_state *);
