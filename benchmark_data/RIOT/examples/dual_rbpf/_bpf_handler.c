#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "net/gcoap.h"
#include "fmt.h"
#include "bpf.h"
#include "bpf/shared.h"
#include "bpf/store.h"

static ssize_t _bpf_counter(coap_pkt_t* pdu, uint8_t *buf, size_t len, void *ctx);
static ssize_t _bpf_state_handler(coap_pkt_t* pdu, uint8_t *buf, size_t len, void *ctx);
static ssize_t _bpf_handler(coap_pkt_t* pdu, uint8_t *buf, size_t len, void *ctx);
static ssize_t _riot_board_handler(coap_pkt_t* pdu, uint8_t *buf, size_t len, void *ctx);
static ssize_t _bpf_submit_handler(coap_pkt_t *pdu, uint8_t *buf, size_t len, void *ctx);

#define GCOAP_BPF_APP_SIZE  4096

static uint8_t _application[GCOAP_BPF_APP_SIZE] = { 0 };
static uint8_t _stack[512] = { 0 };

static bool _locked = true;

/* CoAP resources. Must be sorted by path (ASCII order). */
static const coap_resource_t _resources[] = {
    { "/bpf/counter", COAP_GET, _bpf_counter, NULL },
    { "/bpf/handle", COAP_GET, _bpf_handler, NULL },
    { "/bpf/state", COAP_GET, _bpf_state_handler, NULL },
    { "/bpf/submit", COAP_POST, _bpf_submit_handler, NULL },
    { "/riot/board", COAP_GET, _riot_board_handler, NULL },
};

static gcoap_listener_t _listener = {
    &_resources[0],
    ARRAY_SIZE(_resources),
    NULL,
    NULL
};

static bpf_t _bpf = {
    .application = _application,
    .application_len = 0,
    .stack = _stack,
    .stack_size = sizeof(_stack),
};

static ssize_t _bpf_state_handler(coap_pkt_t *pdu, uint8_t*buf, size_t len, void *ctx)
{
    (void)pdu;
    (void)buf;
    (void)len;
    (void)ctx;
    return -1;
}

static ssize_t _bpf_counter(coap_pkt_t *pdu, uint8_t *buf, size_t len, void *ctx)
{
    (void)ctx;

    uint32_t value = 0;
    char stringified[20];

    bpf_store_fetch_global(0x50, &value);

    size_t str_len = fmt_u32_dec(stringified, value);

    gcoap_resp_init(pdu, buf, len, COAP_CODE_CONTENT);
    coap_opt_add_format(pdu, COAP_FORMAT_TEXT);
    size_t resp_len = coap_opt_finish(pdu, COAP_OPT_FINISH_PAYLOAD);
    if (pdu->payload_len >= str_len) {
        memcpy(pdu->payload, stringified, str_len);
        return resp_len + str_len;
    }
    return gcoap_response(pdu, buf, len, COAP_CODE_INTERNAL_SERVER_ERROR);
}

static ssize_t _bpf_submit_handler(coap_pkt_t *pdu, uint8_t *buf, size_t len, void *ctx)
{
    (void)ctx;
    coap_block1_t block1 = { 0 };

    unsigned resp_code = COAP_CODE_CHANGED;

    int blockwise = coap_get_block1(pdu, &block1);

    printf("[BPF] app block: offset=%u len=%u blockwise=%i more=%i\n",
           (unsigned)block1.offset, pdu->payload_len, blockwise, block1.more);

    if (block1.blknum == 0) {
        /* lock bpf_handler */
        _locked = true;
    }
    if (!block1.more) {
        /* unlock bpf_handler */
        _bpf.application_len = block1.offset + pdu->payload_len;
        _locked = false;
    }
    else {
        resp_code = COAP_CODE_CONTINUE;
    }

    memcpy(_application + block1.offset, pdu->payload, pdu->payload_len);

    gcoap_resp_init(pdu, buf, len, resp_code);

    if (blockwise) {
        coap_opt_add_block1_control(pdu, &block1);
    }
    size_t pdu_len = coap_opt_finish(pdu, COAP_OPT_FINISH_NONE);
    return pdu_len;
}

static ssize_t _bpf_handler(coap_pkt_t *pdu, uint8_t *buf, size_t len, void *ctx)
{
    (void)ctx;

    bpf_mem_region_t mem_pdu;
    bpf_mem_region_t mem_pkt;

    bpf_coap_ctx_t bpf_ctx = {
        .pkt = pdu,
        .buf = buf,
        .buf_len = len,
    };
    printf("[BPF]: executing gcoap handler\n");

    if (_locked) {
        return -1;
    }

    bpf_setup(&_bpf);

    bpf_add_region(&_bpf, &mem_pdu, pdu->hdr, 256, BPF_MEM_REGION_READ | BPF_MEM_REGION_WRITE);
    bpf_add_region(&_bpf, &mem_pkt, pdu, sizeof(coap_pkt_t), BPF_MEM_REGION_READ | BPF_MEM_REGION_WRITE);

    int64_t result = -1;

    uint32_t start = xtimer_now_usec();
    int res = bpf_execute(&_bpf, &bpf_ctx, sizeof(bpf_ctx), &result);
    uint32_t stop = xtimer_now_usec();

    printf("Execution done res=%i, result=%i\n", res, (int)result);
    printf("duration: %"PRIu32" us\n",
           (stop - start));
    return (ssize_t)result;
}

static ssize_t _riot_board_handler(coap_pkt_t* pdu, uint8_t *buf, size_t len, void *ctx)
{
    (void)ctx;
    gcoap_resp_init(pdu, buf, len, COAP_CODE_CONTENT);
    coap_opt_add_format(pdu, COAP_FORMAT_TEXT);
    size_t resp_len = coap_opt_finish(pdu, COAP_OPT_FINISH_PAYLOAD);

    /* write the RIOT board name in the response buffer */
    if (pdu->payload_len >= strlen(RIOT_BOARD)) {
        memcpy(pdu->payload, RIOT_BOARD, strlen(RIOT_BOARD));
        return resp_len + strlen(RIOT_BOARD);
    }
    else {
        puts("gcoap_cli: msg buffer too small");
        return gcoap_response(pdu, buf, len, COAP_CODE_INTERNAL_SERVER_ERROR);
    }
}

void gcoap_bpf_init(void)
{
    gcoap_register_listener(&_listener);
}
