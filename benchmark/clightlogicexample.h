#include<stdio.h>

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
  unsigned int mem_num;
  struct memory_region *mrs;
};
