include ../Makefile.tests_common

USEMODULE += embunit
USEMODULE += bpf
USEMODULE += test_utils_interactive_sync

USEMODULE += ztimer_usec
USEMODULE += saul
USEMODULE += saul_reg
USEMODULE += saul_default
USEMODULE += printf_float
USEMODULE += ps

BLOBS += bpf/average.bin

BPF_COQ ?= 0
CSV ?= 1

ifeq (1,$(BPF_COQ))
EXTERNAL_MODULE_DIRS += external
USEMODULE += gen_bpf
else
USEMODULE += bpf
endif

NUM_ITERATIONS ?= 100 
NUM_VARIABLES ?= 100

CFLAGS += -I$(CURDIR) -DNUM_ITERATIONS=$(NUM_ITERATIONS) -DNUM_VARIABLES=$(NUM_VARIABLES) -DBPF_COQ=$(BPF_COQ)
CFLAGS += -DCSV_OUT=$(CSV)

include $(RIOTBASE)/Makefile.include
