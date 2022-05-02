RIOTBASE ?= ../RIOT
include $(RIOTBASE)/tests/Makefile.tests_common

USEMODULE += embunit
USEMODULE += bpf
USEMODULE += test_utils_interactive_sync

USEMODULE += ztimer_usec
USEMODULE += saul
USEMODULE += saul_reg
USEMODULE += saul_default
USEMODULE += printf_float

BPF_COQ ?= 0
CSV ?= 1

ifeq (1,$(BPF_COQ))
EXTERNAL_MODULE_DIRS += external
USEMODULE += gen_bpf
else
USEMODULE += bpf
endif

NUM_INSTRUCTIONS ?= 2000
BPF_BRANCHES_ALLOWED = $(NUM_INSTRUCTIONS)

CFLAGS += -I$(CURDIR) -DNUM_INSTRUCTIONS=$(NUM_INSTRUCTIONS) -DBPF_COQ=$(BPF_COQ) -DCONFIG_BPF_BRANCHES_ALLOWED=$(BPF_BRANCHES_ALLOWED)
CFLAGS += -DCSV_OUT=$(CSV)

include $(RIOTBASE)/Makefile.include
