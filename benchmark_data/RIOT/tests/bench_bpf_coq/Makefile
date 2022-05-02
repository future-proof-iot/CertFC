include ../Makefile.tests_common

USEMODULE += embunit
USEMODULE += bpf

USEMODULE += ztimer_usec
USEMODULE += saul
USEMODULE += saul_reg
USEMODULE += saul_default
USEMODULE += printf_float

EXTERNAL_MODULE_DIRS += external
USEMODULE += gen_bpf

CFLAGS += -I$(CURDIR)

include $(RIOTBASE)/Makefile.include
