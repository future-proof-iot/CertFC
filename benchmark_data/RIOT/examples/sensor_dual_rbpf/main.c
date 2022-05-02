/*
 * Copyright (c) 2015-2016 Ken Bannister. All rights reserved.
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
 * @brief       gcoap example
 *
 * @author      Ken Bannister <kb2ma@runbox.com>
 *
 * @}
 */

#include <stdio.h>
#include "msg.h"

#include "net/gcoap.h"
#include "kernel_types.h"
#include "shell.h"

#include "bpf.h"
#include "blob/bpf/sensor_process.bin.h"

#define MAIN_QUEUE_SIZE (4)
static msg_t _main_msg_queue[MAIN_QUEUE_SIZE];
static uint8_t _bpf_stack[512];
static char _stack[THREAD_STACKSIZE_MAIN];

extern void gcoap_bpf_init(void);


static void *_counter_thread(void *arg)
{
    /* Starts a long running bpf thread */
    (void)arg;
    bpf_t bpf = {
        .application = sensor_process_bin,
        .application_len = sizeof(sensor_process_bin),
        .stack = _bpf_stack,
        .stack_size = sizeof(_bpf_stack),
        .flags = BPF_CONFIG_NO_RETURN,
    };
    unsigned int ctx = 0;
    int64_t result = 0;
    bpf_setup(&bpf);
    int res = bpf_execute(&bpf, &ctx, sizeof(ctx), &result);

    printf("Return code: %d\n", res);

    assert(false);
    return NULL;
}

int main(void)
{
    /* for the thread running the shell */
    msg_init_queue(_main_msg_queue, MAIN_QUEUE_SIZE);
    puts("gcoap example app");

    bpf_init();
    thread_create(_stack,
                  sizeof(_stack),
                  THREAD_PRIORITY_MAIN - 1,
                  THREAD_CREATE_STACKTEST,
                  _counter_thread,
                  NULL,
                  "bpf long");

    gcoap_bpf_init();

    /* start shell */
    puts("All up, running the shell now");
    char line_buf[SHELL_DEFAULT_BUFSIZE];
    shell_run(NULL, line_buf, SHELL_DEFAULT_BUFSIZE);

    /* should never be reached */
    return 0;
}
