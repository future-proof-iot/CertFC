#include <stdint.h>
#include "bpf/bpfapi/helpers.h"

#define SHARED_KEY 0x50
#define PERIOD_US (1000 * 1000)

int periodic_incr(bpf_coap_ctx_t *gcoap)
{
    uint32_t last_wakeup = bpf_ztimer_now();

    uint32_t counter = 0;

    while (1) {
        bpf_fetch_global(SHARED_KEY, &counter);
        counter++;
        bpf_store_global(SHARED_KEY, counter);
        bpf_ztimer_periodic_wakeup(&last_wakeup, PERIOD_US);
    }

    return 0;
}

