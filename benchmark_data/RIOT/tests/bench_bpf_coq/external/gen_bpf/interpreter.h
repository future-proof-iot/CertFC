#include<stdio.h>
#include<stdint.h>

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
  uint64_t start_addr;
  uint64_t block_size;
};

struct memory_regions {
  struct memory_region* bpf_ctx;
  struct memory_region* bpf_stk;
  struct memory_region* content;
};

struct bpf_state {
  uint64_t state_pc;
  uint64_t regsmap[11];
  int bpf_flag;
  struct memory_regions *mrs;
};


uint64_t bpf_interpreter(struct bpf_state *, const uint64_t *, uint64_t, uint32_t);
