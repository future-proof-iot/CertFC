/*
 * Copyright (C) 2021 Inria
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @defgroup    sched_rbpf rbpf scheduler hook
 * @ingroup     sys
 *
 * @{
 *
 * @file
 * @brief       Scheduler rbpf callback
 *
 * @author      Koen Zandberg <koen@bergzand.net>
 */

#ifndef SCHED_RBPF
#define SCHED_RBPF

#include <stdint.h>
#include "kernel_defines.h"
#include "bpf.h"

#ifdef __cplusplus
 extern "C" {
#endif

/**
 *  Scheduler statistics
 */
typedef struct {
    uint64_t previous;
    uint64_t next;
} sched_ctx_t;


/**
 *  @brief  Registers the sched rbpf callback and sets laststart for
 *          caller thread
 */
void init_sched_rbpf(void);

void sched_rbpf_add_hook(bpf_hook_t *hook);
#ifdef __cplusplus
}
#endif

#endif /* SCHED_RBPF_H */
/** @} */

