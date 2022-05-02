/*
 * Copyright (c) 2021 Koen Zandberg
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     examples
 * @{
 *
 * @file
 * @brief       Minimal bpf example
 *
 * @author      Koen Zandberg <koen.zandberg@inria.fr>
 *
 * @}
 */
#include <stdio.h>

#include "bpf.h"
#include "blob/bpf/increment.bin.h"

static uint8_t _stack[512] = { 0 };

int main(void)
{
    bpf_init();

    puts("All up, running the rBPF VM now");

    bpf_t bpf = {
        .application = increment_bin,
        .application_len = sizeof(increment_bin),
        .stack = _stack,
        .stack_size = sizeof(_stack),
    };

    unsigned int ctx = 4;
    int64_t result = 0;

    bpf_setup(&bpf);
    int res = bpf_execute(&bpf, (void*)ctx, sizeof(ctx), &result);

    printf("Return code: %d\n", res);
    printf("Result: %ld\n", (unsigned long)result);

    /* should never be reached */
    return 0;
}
