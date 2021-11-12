#include <stdio.h>
#include <inttypes.h>
#include "interpreter.h"
#include "fletcher32_bpf.h"
#include<stdlib.h>
#include<stddef.h>
#include <time.h> 

uint32_t fletcher32(const uint16_t *data, size_t words)
{
    uint32_t sum1 = 0xffff, sum2 = 0xffff, sumt = 0xffff;

    while (words) {
        unsigned tlen = words > 359 ? 359 : words;
        words -= tlen;
        do {
            sumt = sum1;
            sum2 += sum1 += *data++;
        } while (--tlen);
        sum1 = (sum1 & 0xffff) + (sum1 >> 16);
        sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    }
    sum1 = (sum1 & 0xffff) + (sum1 >> 16);
    sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    return (sum2 << 16) | sum1;
}

static const unsigned char wrap_around_data[] =
        "AD3Awn4kb6FtcsyE0RU25U7f55Yncn3LP3oEx9Gl4qr7iDW7I8L6Pbw9jNnh0sE4DmCKuc"
        "d1J8I34vn31W924y5GMS74vUrZQc08805aj4Tf66HgL1cO94os10V2s2GDQ825yNh9Yuq3"
        "QHcA60xl31rdA7WskVtCXI7ruH1A4qaR6Uk454hm401lLmv2cGWt5KTJmr93d3JsGaRRPs"
        "4HqYi4mFGowo8fWv48IcA3N89Z99nf0A0H2R6P0uI4Tir682Of3Rk78DUB2dIGQRRpdqVT"
        "tLhgfET2gUGU65V3edSwADMqRttI9JPVz8JS37g5QZj4Ax56rU1u0m0K8YUs57UYG5645n"
        "byNy4yqxu7";


struct fletcher32_ctx {
  const unsigned short * data;
  unsigned int words;
};

struct fletcher32_ctx f32_ctx = {
  .data = (const unsigned short *) wrap_around_data,
  .words = sizeof(wrap_around_data)/2,
};

//struct memory_regions *memory_regions = &init_memory_regions;

static void bpf_add_region_ctx(struct bpf_state* st){
  (*(*((*st).mrs)).bpf_ctx).start_addr = (unsigned long long) &f32_ctx;
  (*(*((*st).mrs)).bpf_ctx).block_size = sizeof(f32_ctx);
}

void bpf_add_region_content(struct bpf_state* st){
  (*(*((*st).mrs)).content).start_addr = (unsigned long long) (const uint16_t *)wrap_around_data;
  (*(*((*st).mrs)).content).block_size = sizeof(wrap_around_data);
}

/*
void print_region_ctx(){
  printf("start_ctx = %lld\n", (const unsigned short *)(uintptr_t) memory_regions.bpf_ctx.start_addr);
  printf("ctx_size = %lld\n", memory_regions.bpf_ctx.block_size);
  printf("ctx_words = %lld\n", ((unsigned short *)(uintptr_t) (memory_regions.bpf_ctx.start_addr+8)));
  printf("ctx_words = %lld\n", *((unsigned short *)(uintptr_t) (memory_regions.bpf_ctx.start_addr+8)));
}

void print_region_content(){
  printf("content_start_addr = %" PRIu64 "\n", memory_regions.content.start_addr);
  printf("content_start = %" PRIu64 "\n", * (const uint16_t *) memory_regions.content.start_addr);
  printf("content_size = %" PRIu64 "\n", memory_regions.content.block_size);
}

void print_normal_addr(){
  printf("\n\n *********print_normal_addr*******\n\n");
  printf("sizeof(bpf_fletcher32_bpf_bin) = %d\n", sizeof(bpf_fletcher32_bpf_bin));
  
  printf("start_f32_ctx       = %lld\n", &f32_ctx);
  printf("start_f32_ctx.data  = %lld\n", &(f32_ctx.data));
  printf("start_f32_ctx.words = %lld\n", f32_ctx.words);
  printf("start_f32_ctx.words = %lld\n", &(f32_ctx.words));
  
  for (int i = 0; i < 10; i++) {
  	printf("%0d:", i);
  	printf("ins64        = %" PRIu64 "\n", *((unsigned long long *) bpf_fletcher32_bpf_bin +i));
  }
  printf("\n\n *********print_normal_addr*******\n\n");
}
*/

int main(){
  
  printf("Hello rBPF_fletcher32 C code Testing:\n");
  uint32_t res0;    
  //printf("start_content:%d\n", (const uint16_t *) wrap_around_data);
  //printf("start_addr_content:%d\n", *wrap_around_data);
  //printf("start_addr_content1:%d\n", *(const uint16_t *) wrap_around_data);
  // printf("size_content:%d\n", sizeof(wrap_around_data)/2);
  clock_t begin0 = clock();
  //for (int i = 0; i < 1000; i++) {
    res0 = fletcher32((const uint16_t *) wrap_around_data, sizeof(wrap_around_data)/2);
    //}
  clock_t end0 = clock();
  printf("execution time:%f\n", (double)(end0-begin0)/CLOCKS_PER_SEC);
  printf("rBPF_fletcher32 C result = 0x:%x\n", res0);

  printf("End rBPF_fletcher32 Testing!\n");

  

  printf ("fletcher32 start!!! \n");
  unsigned long long result;
  // adding memory_regions
  static struct memory_region init_memory_region0 = {.start_addr = 0LLU, .block_size = 0LLU }; 
  static struct memory_region init_memory_region1 = {.start_addr = 0LLU, .block_size = 0LLU }; 
  static struct memory_region init_memory_region2 = {.start_addr = 0LLU, .block_size = 0LLU }; 

  static struct memory_regions init_memory_regions = {
    .bpf_ctx = &init_memory_region0,
    .bpf_stk = &init_memory_region1,
    .content = &init_memory_region2
  };

  struct bpf_state st = {
    .state_pc = 0LLU,
    .regsmap = {0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU},
    .bpf_flag = BPF_OK,
    .mrs = &init_memory_regions
  };
  
  bpf_add_region_ctx(&st);
  bpf_add_region_content(&st);
  
  clock_t begin1 = clock();
  //for (int j = 0; j < 1000; j++) { //TODO: why a loop returns a wrong result? 
    result = bpf_interpreter(&st, (unsigned long long *) bpf_fletcher32_bpf_bin, sizeof(bpf_fletcher32_bpf_bin), 10000);
    //}
  clock_t end1 = clock();
  printf("execution time:%f\n", (double)(end1-begin1)/CLOCKS_PER_SEC);
  
  printf("rBPF_fletcher32 (dx) C result = 0x:%x\n", (unsigned int)result);
  printf ("fletcher32 end!!! \n");
  return 0;
}


