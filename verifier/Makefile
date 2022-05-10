include Makefile.config

SED := sed
CAT := cat
AWK := awk
COQC := coqc
COQDEP := coqdep
OCAMLOPT := ocamlopt
COQMAKEFILE := coq_makefile
CP := cp

CC=gcc
OFLAGS=-Os
CLIGHTGEN=clightgen
CLIGHTGEN32=$(CLIGHTGEN32DIR)/clightgen


verifier-all:
	@echo $@
	@$(MAKE) verifier-extract
	@$(MAKE) verifier-repatch
	@$(MAKE) verifier-clightmodel

verifier-extract:
	@echo $@
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I dxmodel dxmodel/verifier_TestMain.mli	
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I dxmodel -c dxmodel/verifier_TestMain.ml
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -args $(DXDIR)/cprinter-link-args dxmodel/verifier_TestMain.cmx -o dxmodel/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini dxmodel/compcert.ini
	cd dxmodel && ./main

verifier-repatch:
	@echo $@
	$(CP) dxmodel/generated.c repatch
	cd repatch && $(CC) -o repatch1 repatch1.c && ./repatch1 && $(CC) -o repatch2 repatch2.c && ./repatch2 && $(CC) -o repatch3 repatch3.c && ./repatch3 && $(CC) -o repatch4 repatch4.c && ./repatch4
	$(CP) repatch/verifier.c clightmodel

verifier-clightmodel:
	@echo $@
	cd clightmodel && $(CC) -o $@ $(OFLAGS) fletcher32_verifier_test.c verifier.c && ./$@
	cd clightmodel && $(CLIGHTGEN32) verifier.c

.PHONY: verifier-all verifier-extract verifier-repatch verifier-clightmodel
