/*
 * Copyright (C) 2021 Inria
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     sys_shell_commands
 * @{
 *
 * @file
 * @brief       Provides shell commands to manage and show rbpf storage values
 *
 * @author      Koen Zandberg <koen@bergzand.net>
 *
 * @}
 */
#include <string.h>
#include <stdio.h>

#include "btree.h"
#include "bpf.h"
#include "bpf/store.h"


void _print_node(btree_node_t *node, size_t depth, void *ctx)
{
    (void)depth;
    (void)ctx;
    bpf_store_keyval_t *keyval = (bpf_store_keyval_t*)node;
    printf("| %5d | %5d |\n", bpf_store_get_key(keyval), bpf_store_get_value(keyval));
}

int _sc_bpf(int argc, char **argv)
{
    (void)argv;
    if (argc == 1) {
        printf("+-------+-------+\n");
        printf("| key   | value |\n");
        printf("+-------+-------+\n");
        bpf_store_iter_global(_print_node, NULL);
        printf("+-------+-------+\n");
    }
    return 0;
}

