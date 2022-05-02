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
#include "bpf.h"
#include "bpf/store.h"
#include "embUnit.h"

#include "blob/bpf/sample.bin.h"
#include "blob/bpf/sample_storage.bin.h"
#include "blob/bpf/sample_saul.bin.h"

#define BPF_SAMPLE_STORAGE_KEY_A  5
#define BPF_SAMPLE_STORAGE_KEY_B  15
#define BPF_SAMPLE_STORAGE_KEY_C  3
#define BPF_SAMPLE_STORAGE_KEY_SENSE  1

static uint8_t _bpf_stack[512];

static void _init(void)
{
    bpf_init();
}

static void tests_bpf_run_ctx(void)
{
    bpf_t bpf = {
        .application = sample_bin,
        .application_len = sizeof(sample_bin),
        .stack = _bpf_stack,
        .stack_size = sizeof(_bpf_stack),
    };
    unsigned int ctx = 8;
    int64_t result = 0;
    bpf_setup(&bpf);
    TEST_ASSERT_EQUAL_INT(0, bpf_execute_ctx(&bpf, &ctx, sizeof(ctx), &result));
    TEST_ASSERT_EQUAL_INT(16, (int)result);
}

static void tests_bpf_storage(void)
{
    bpf_t bpf = {
        .application = sample_storage_bin,
        .application_len = sizeof(sample_storage_bin),
        .stack = _bpf_stack,
        .stack_size = sizeof(_bpf_stack),
    };
    unsigned int ctx = 8;
    int64_t result = 0;
    bpf_setup(&bpf);
    TEST_ASSERT_EQUAL_INT(0, bpf_execute(&bpf, &ctx, sizeof(ctx), &result));

    uint32_t val;
    bpf_store_fetch_local(&bpf, BPF_SAMPLE_STORAGE_KEY_A, &val);
    TEST_ASSERT_EQUAL_INT(1, val);

    bpf_store_fetch_local(&bpf, BPF_SAMPLE_STORAGE_KEY_B, &val);
    TEST_ASSERT_EQUAL_INT(2, val);

    bpf_store_fetch_local(&bpf, BPF_SAMPLE_STORAGE_KEY_C, &val);
    TEST_ASSERT_EQUAL_INT(3, val);

    /* Second execution */
    TEST_ASSERT_EQUAL_INT(0, bpf_execute(&bpf, &ctx, sizeof(ctx), &result));
    bpf_store_fetch_local(&bpf, BPF_SAMPLE_STORAGE_KEY_A, &val);
    TEST_ASSERT_EQUAL_INT(2, val);
    bpf_store_fetch_local(&bpf, BPF_SAMPLE_STORAGE_KEY_B, &val);
    TEST_ASSERT_EQUAL_INT(6, val);
    bpf_store_fetch_local(&bpf, BPF_SAMPLE_STORAGE_KEY_C, &val);
    TEST_ASSERT_EQUAL_INT(8, val);
}

static void tests_bpf_saul(void)
{
    bpf_t bpf = {
        .application = sample_saul_bin,
        .application_len = sizeof(sample_saul_bin),
        .stack = _bpf_stack,
        .stack_size = sizeof(_bpf_stack),
    };
    unsigned int ctx = 0;
    int64_t result = 0;
    bpf_setup(&bpf);
    TEST_ASSERT_EQUAL_INT(0, bpf_execute(&bpf, &ctx, sizeof(ctx), &result));

    TEST_ASSERT_EQUAL_INT(0, result);

    uint32_t val = 0;
    bpf_store_fetch_local(&bpf, BPF_SAMPLE_STORAGE_KEY_SENSE, &val);
    printf("BPF saul val: %"PRIu32"\n", val);
}


Test *tests_bpf(void)
{
    EMB_UNIT_TESTFIXTURES(fixtures) {
        new_TestFixture(tests_bpf_run_ctx),
        new_TestFixture(tests_bpf_storage),
        new_TestFixture(tests_bpf_saul),
    };

    EMB_UNIT_TESTCALLER(bpf_tests, _init, NULL, fixtures);
    return (Test*)&bpf_tests;
}

int main(void)
{
    TESTS_START();
    TESTS_RUN(tests_bpf());
    TESTS_END();

    return 0;
}
