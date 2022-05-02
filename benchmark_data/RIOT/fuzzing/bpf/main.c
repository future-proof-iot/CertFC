/*
 * Copyright (C) 2021 Inria
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

#include <err.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include "bpf.h"

#define READ_BUFFER_SIZE 2048

static uint8_t _stack[512] = { 0 };

int main(void)
{
    ssize_t read_size;
    uint8_t buffer[READ_BUFFER_SIZE];

    read_size = read(STDIN_FILENO, buffer, READ_BUFFER_SIZE);
    if (read_size < 0) {
        return read_size;
    }

    bpf_init();

    bpf_t bpf = {
        .application = buffer,
        .application_len = read_size,
        .stack = _stack,
        .stack_size = sizeof(_stack),
    };

    unsigned int ctx = 0;
    int64_t result = 0;

    bpf_setup(&bpf);
    int res = bpf_execute(&bpf, (void*)ctx, sizeof(ctx), &result);

    printf("Return code: %d\n", res);
    printf("Result: %ld\n", (unsigned long)result);

    exit(0);
    return EXIT_SUCCESS;
}
