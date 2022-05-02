/*
 * Copyright (C) 2020 Inria
 * Copyright (C) 2020 Koen Zandberg <koen@bergzand.net>
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     tests
 * @{
 *
 * @file
 * @brief       Tests bpf virtual machine
 *
 * @author      Koen Zandberg <koen@bergzand.net>
 *
 * @}
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include "embUnit.h"
#include "timex.h"
#include "ztimer.h"
#include "bpf/shared.h"
#include "bpf/instruction.h"
#include "unaligned.h"

#include "bpf.h"
#if BPF_COQ
#include "interpreter.h"
#else
#include "bpf.h"
#endif

#include "blob/bpf/average.bin.h"

typedef struct {
    uint32_t num_variables;
    uint32_t values[NUM_VARIABLES];
} averaging_ctx_t;

static uint8_t _bpf_stack[512];

static averaging_ctx_t ctx = { 0 };
#if BPF_COQ
static struct memory_region mr_ctx = {.start_addr = (uintptr_t)&ctx,
                                        .block_size = sizeof(ctx),
                                        .block_perm = Readable,
                                        .block_ptr = (unsigned char *)(uintptr_t)&ctx};

static struct memory_region mr_stack = {.start_addr = (uintptr_t)_bpf_stack,
                                        .block_size = sizeof(_bpf_stack),
                                        .block_perm = Freeable,
                                        .block_ptr = _bpf_stack};
#endif


int main(void)
{
#if CSV_OUT
    puts("test,duration,code,usperexec,kexecspersec");
#else
    printf("| %-5s | %-8s | %-6s | %-6s | %-16s |\n",
           "Test", "duration", "code", "us/exec", "execs per sec");
#endif
    for (size_t test_idx = 1; test_idx <= NUM_VARIABLES; test_idx++) {
        ctx.num_variables = test_idx;
#if BPF_COQ
        struct memory_region memory_regions[] = { mr_ctx, mr_stack };
        rbpf_header_t *header = (rbpf_header_t*)average_bin;
        const void * text = (uint8_t*)header + sizeof(rbpf_header_t) + header->data_len + header->rodata_len;

#else
        bpf_t bpf = {
            .application = (uint8_t*)average_bin,
            .application_len = sizeof(average_bin),
            .stack = _bpf_stack,
            .stack_size = sizeof(_bpf_stack),
        };
        bpf_setup(&bpf);
        int64_t res = 0;
#endif

        uint32_t begin = ztimer_now(ZTIMER_USEC); // unsigned long long -> uint64_t
        volatile int result = 0;
        for (size_t i = 0; i < NUM_ITERATIONS; i++) {
#if BPF_COQ
            struct bpf_state st = {
                .state_pc = 0,
                .regsmap = {0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, 0LLU, (intptr_t)_bpf_stack+512},
                .bpf_flag = vBPF_OK,
                .mrs = memory_regions,
                .mrs_num = ARRAY_SIZE(memory_regions),
                .ins = text,
                .ins_len = header->text_len,
            };
            result = bpf_interpreter(&st, 10000);
            result = st.bpf_flag;
#else
            result = bpf_execute_ctx(&bpf, &ctx, sizeof(ctx), &res);
#endif
        }
        uint32_t end = ztimer_now(ZTIMER_USEC);
        float duration = (float)(end-begin);
        float us_per_op = duration/NUM_ITERATIONS;
        float kops_per_sec = (float)(NUM_ITERATIONS*US_PER_MS) / duration;
#if CSV_OUT
        printf("%u,%f,%d,%f,%f\n",
#else
        printf("| %5u | %2.4fms | %6d | %2.4fus | %7.2f kops/sec |\n",
#endif
                test_idx,
                duration/US_PER_MS, (signed)result, us_per_op, kops_per_sec);
    }

    return 0;
}
