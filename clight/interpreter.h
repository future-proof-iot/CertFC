#include<stdio.h>

/*                                                                              
defining bpf_flag                                                               
 */

enum BPF_FLAG {
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

/*                                                                              
defining bpf_permission                                                               
 */

enum BPF_PERM {
    Freeable = 3,
    Writable = 2,
    Readable = 1,
    Nonempty = 0,
};

struct memory_region {
  unsigned long long start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned long long block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned int mem_num;
  unsigned long long regsmap[11];
  struct memory_region *mrs;
};

void add_mem_region(struct bpf_state *, struct memory_region *);

void add_mem_region_ctx(struct bpf_state *, struct memory_region *);

unsigned long long bpf_interpreter(struct bpf_state *, int, unsigned int, unsigned long long *);

