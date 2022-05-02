/*
 * Copyright (C) 2021 Inria
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     sys
 * @{
 *
 * @file
 * @brief       Scheduler rbpf hook implementation
 *
 * @author      Koen Zandberg <koen@bergzand.net>
 *
 * @}
 */

#include "sched.h"
#include "thread.h"
#include "irq.h"
#include "sched_rbpf.h"
#include "bpf.h"

static uint8_t _stack[BPF_STACK_SIZE];

static void sched_rbpf_cb(kernel_pid_t active_thread, kernel_pid_t next_thread)
{
    sched_ctx_t ctx = {
        .previous = active_thread,
        .next = next_thread,
    };

    int64_t res;

    bpf_hook_execute(BPF_HOOK_SCHED, &ctx, sizeof(ctx), &res);
    (void)res;
}

void init_sched_rbpf(void)
{
    /* Init laststart for the thread starting schedstatistics since the callback
       wasn't registered when it was first scheduled */
    sched_register_cb(sched_rbpf_cb);
}

void sched_rbpf_add_hook(bpf_hook_t *hook)
{
    unsigned state = irq_disable();

    hook->application->stack = _stack;
    hook->application->stack_size = sizeof(_stack);
    bpf_setup(hook->application);
    bpf_hook_install(hook, BPF_HOOK_SCHED);

    irq_restore(state);
}
