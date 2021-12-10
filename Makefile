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

THIS_FILE := $(lastword $(MAKEFILE_LIST))

# Disable warnings on notations (that are coming from the standard
# library)
COQPROJOPTS := $(shell $(CAT) _CoqProject)
COQDEPOPTS := $(COQPROJOPTS)
COQCOPTS := $(COQPROJOPTS) -w all,-notation
COQEXTROPTS :=  -R ../tests dx.tests -w all,-extraction

OCAMLINCS := -I extr # -I src

test:
	@echo $@
	@$(MAKE) compile
	@$(MAKE) extract
	@$(MAKE) repatch

all:
	@echo $@
	@$(MAKE) compile
	@$(MAKE) extract
	@$(MAKE) clight
	@$(MAKE) proof 



COQSRC = $(wildcard tests/*.v)

compile:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQSRC) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile
	$(CP) TestMain.ml tests # mv -> cp to avoid when running `make` again, it doesn't find the two files
	$(CP) TestMain.mli tests

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
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.cmxa
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.a
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(DXDIR)/extr/ResultMonad.cmx $(DXDIR)/extr/DXModule.cmx $(DXDIR)/extr/DumpAsC.cmx tests/TestMain.cmx -o tests/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini tests/compcert.ini
	cd tests && ./main

repatch:
	@echo $@
	$(CP) tests/generated.c repatch
	cd repatch && $(CC) -o $@ repatch.c && ./repatch

clight:
	@echo $@
	cd codeTest && $(CC) -o $@ $(OFLAGS) fletcher32_bpf_test.c interpreter.c
	cd codeTest && $(CLIGHTGEN) interpreter.c

PROOF = $(addprefix codeTest/,clight_exec.v Clightlogic.v interpreter.v CommonLemma.v MatchState.v CorrectRel.v correct_is_well_chunk_bool.v correct_upd_pc.v correct_eval_pc.v correct_upd_pc_incr.v correct_eval_reg.v correct_upd_reg.v correct_eval_flag.v correct_upd_flag.v correct_getMemRegion_block_ptr.v correct_getMemRegion_block_size.v correct_getMemRegion_start_addr.v correct_get_addl.v correct_get_subl.v correct_check_mem_aux.v)

proof:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(PROOF) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefilePrf
	make -f CoqMakefilePrf

clean :
	@echo $@
	find . -name "*\.vo" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;


# We want to keep the .cmi that were built as we go
.SECONDARY:

.PHONY: all compile extract repatch clight proof clean
