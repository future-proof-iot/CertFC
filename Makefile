include Makefile.config

SED := sed
CAT := cat
AWK := awk
COQC := coqc
COQDEP := coqdep
OCAMLOPT := ocamlopt

CC=gcc
OFLAGS=-Os
CLIGHTGEN=clightgen

THIS_FILE := $(lastword $(MAKEFILE_LIST))

# Disable warnings on notations (that are coming from the standard
# library)
COQPROJOPTS := $(shell $(CAT) _CoqProject)
COQDEPOPTS := $(COQPROJOPTS)
COQCOPTS := $(COQPROJOPTS) -w all,-notation
COQEXTROPTS :=  -R ../tests dx.tests -w all,-extraction

OCAMLINCS := -I extr # -I src

all:
	@echo $@
	@$(MAKE) compile
	@$(MAKE) extract
	@$(MAKE) clight
	@$(MAKE) proof 


compile:
	@echo $@
	$(COQC) $(COQCOPTS) tests/Int16.v
	$(COQC) $(COQCOPTS) tests/CoqIntegers.v
	$(COQC) $(COQCOPTS) tests/InfComp.v
	$(COQC) $(COQCOPTS) tests/DxIntegers.v
	$(COQC) $(COQCOPTS) tests/DxFlag.v
	$(COQC) $(COQCOPTS) tests/DxList64.v
	$(COQC) $(COQCOPTS) tests/DxValues.v
	$(COQC) $(COQCOPTS) tests/IdentDef.v
	$(COQC) $(COQCOPTS) tests/DxRegs.v
	$(COQC) $(COQCOPTS) tests/DxMemRegion.v
	$(COQC) $(COQCOPTS) tests/GenMatchable.v
	$(COQC) $(COQCOPTS) tests/DxOpcode.v
	$(COQC) $(COQCOPTS) tests/DxState.v
	$(COQC) $(COQCOPTS) tests/DxMonad.v
	$(COQC) $(COQCOPTS) tests/DxAST.v
	$(COQC) $(COQCOPTS) tests/DxInstructions.v
	$(COQC) $(COQCOPTS) tests/Tests.v
	$(COQC) $(COQCOPTS) tests/TestMain.v
	cd tests/ && $(COQC) $(COQEXTROPTS) ExtrMain.v

extract:
	@echo $@
	
	$(COMPCERTSRCDIR)/tools/modorder $(COMPCERTSRCDIR)/.depend.extr cfrontend/PrintCsyntax.cmx | \
	    $(AWK) '{ delete paths ;                                                                 \
	              for(i = 1; i <= NF; i++) {                                                     \
	                 x = $$i ;                                                                   \
	                 sub("/[^/]*$$", "", x) ;                                                    \
	                 paths[x] = 1 ;                                                              \
	              }                                                                              \
	              for(p in paths) {                                                              \
	                 print "-I" ;                                                                \
	                 print "$(COMPCERTSRCDIR)/" p ;                                              \
	              }                                                                              \
	            }' > compcertsrc-I	
	$(COMPCERTSRCDIR)/tools/modorder $(COMPCERTSRCDIR)/.depend.extr cfrontend/PrintCsyntax.cmx | \
	    $(AWK) 'BEGIN { RS=" " } /cmx/ { gsub(".*/","") ; print }' > compcertcprinter-cmx-args
	
	$(OCAMLOPT) -args compcertsrc-I -I $(DXDIR)/extr -I $(DXDIR)/src -I tests tests/TestMain.mli	
	$(OCAMLOPT) -args compcertsrc-I -I $(DXDIR)/extr -I $(DXDIR)/src -I tests -c tests/TestMain.ml
		
	$(OCAMLOPT) -args compcertsrc-I -I $(DXDIR)/extr -c $(DXDIR)/src/DumpAsC.ml
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.cmxa
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.a
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(DXDIR)/extr/ResultMonad.cmx $(DXDIR)/extr/DXModule.cmx $(DXDIR)/extr/DumpAsC.cmx tests/TestMain.cmx -o tests/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini tests/compcert.ini
	cd tests && ./main

clight:
	@echo $@
	cd codeTest && $(CC) -o $@ $(OFLAGS) fletcher32_bpf_test.c interpreter.c
	
	cd codeTest && $(CLIGHTGEN) interpreter.c

proof:
	@echo $@
	$(COQC) $(COQCOPTS) codeTest/interpreter.v
	$(COQC) $(COQCOPTS) codeTest/CommonLemma.v
	$(COQC) $(COQCOPTS) codeTest/MatchState.v
	$(COQC) $(COQCOPTS) codeTest/clight_exec.v
	$(COQC) $(COQCOPTS) codeTest/Clightlogic.v

clean :
	@echo $@
	find . -name "*\.vo" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;


# We want to keep the .cmi that were built as we go
.SECONDARY:

.PHONY: all compile extract clight proof clean
