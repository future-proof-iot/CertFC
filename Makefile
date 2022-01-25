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

THIS_FILE := $(lastword $(MAKEFILE_LIST))

# Disable warnings on notations (that are coming from the standard
# library)
COQPROJOPTS := $(shell $(CAT) _CoqProject)
COQDEPOPTS := $(COQPROJOPTS)
COQCOPTS := $(COQPROJOPTS) -w all,-notation
COQEXTROPTS :=  -R ../src dx.src -w all,-extraction

OCAMLINCS := -I extr # -I src

all:
	@echo $@
	@$(MAKE) comm
	@$(MAKE) model
	@$(MAKE) monadicmodel
	@$(MAKE) compile
	@$(MAKE) extract
	@$(MAKE) repatch
	@$(MAKE) clightmodel
	@$(MAKE) clightlogic
	@$(MAKE) simulation
	@$(MAKE) isolation
	@$(MAKE) equivalence


BENCHSRC = $(wildcard benchmark/*.v)

bench:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(BENCHSRC) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile
	$(CP) BenchmarkTestMain.ml benchmark
	$(CP) BenchmarkTestMain.mli benchmark
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
	$(OCAMLOPT) -args compcertsrc-I -I $(DXDIR)/extr -I $(DXDIR)/src -I benchmark benchmark/BenchmarkTestMain.mli	
	$(OCAMLOPT) -args compcertsrc-I -I $(DXDIR)/extr -I $(DXDIR)/src -I benchmark -c benchmark/BenchmarkTestMain.ml
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.cmxa
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.a
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(DXDIR)/extr/ResultMonad.cmx $(DXDIR)/extr/DXModule.cmx $(DXDIR)/extr/DumpAsC.cmx benchmark/BenchmarkTestMain.cmx -o benchmark/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini benchmark/compcert.ini
	cd benchmark && ./main

bench_clight:
	@echo $@
	cd benchmark && $(CLIGHTGEN32) clightlogicexample.c

COQMODEL =  $(addprefix model/, Syntax.v Decode.v Semantics.v)
COQEMONADIC =  $(addprefix monadicmodel/, Opcode.v rBPFInterpreter.v)
COQSRC =  $(addprefix src/, InfComp.v GenMatchable.v CoqIntegers.v DxIntegers.v DxValues.v DxNat.v DxAST.v DxFlag.v DxList64.v DxOpcode.v IdentDef.v DxMemType.v DxMemRegion.v DxRegs.v DxState.v DxMonad.v DxInstructions.v Tests.v TestMain.v ExtrMain.v)
COQEQUIV =  $(addprefix equivalence/, switch.v equivalence1.v equivalence2.v)
COQISOLATION = $(addprefix isolation/, CommonISOLib.v AlignChunk.v RegsInv.v MemInv.v IsolationLemma.v Isolation.v)

COQCOMM = $(wildcard comm/*.v)
#COQMODEL = $(wildcard model/*.v)
#COQSRC = $(wildcard src/*.v)

comm:
	@echo $@
#	rm -f comm/*.vo
	$(COQMAKEFILE) -f _CoqProject $(COQCOMM) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile

model:
	@echo $@
#	rm -f model/*.vo
	$(COQMAKEFILE) -f _CoqProject $(COQMODEL) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile

monadicmodel:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQEMONADIC) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile

isolation:
	@echo $@
#	rm -f isolation/*.vo
	$(COQMAKEFILE) -f _CoqProject $(COQISOLATION) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile

equivalence:
	@echo $@
#	rm -f equivalence/*.vo
	$(COQMAKEFILE) -f _CoqProject $(COQEQUIV) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile

compile:
	@echo $@
#	rm -f src/*.vo
	$(COQMAKEFILE) -f _CoqProject $(COQSRC) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile
	$(CP) TestMain.ml src # mv -> cp to avoid when running `make` again, it doesn't find the two files
	$(CP) TestMain.mli src

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
	$(OCAMLOPT) -args compcertsrc-I -I $(DXDIR)/extr -I $(DXDIR)/src -I src src/TestMain.mli	
	$(OCAMLOPT) -args compcertsrc-I -I $(DXDIR)/extr -I $(DXDIR)/src -I src -c src/TestMain.ml
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.cmxa
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.a
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(DXDIR)/extr/ResultMonad.cmx $(DXDIR)/extr/DXModule.cmx $(DXDIR)/extr/DumpAsC.cmx src/TestMain.cmx -o src/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini src/compcert.ini
	cd src && ./main

repatch:
	@echo $@
	$(CP) src/generated.c repatch
	cd repatch && $(CC) -o repatch1 repatch1.c && ./repatch1 && $(CC) -o repatch2 repatch2.c && ./repatch2 && $(CC) -o repatch3 repatch3.c && ./repatch3 && $(CC) -o repatch4 repatch4.c && ./repatch4
	$(CP) repatch/interpreter.c clight

clightmodel:
	@echo $@
	cd clight && $(CC) -o $@ $(OFLAGS) fletcher32_bpf_test.c interpreter.c # && ./$@
	cd clight && $(CLIGHTGEN32) interpreter.c
	$(COQMAKEFILE) -f _CoqProject clight/interpreter.v COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefile
	make -f CoqMakefile

PROOF = $(addprefix simulation/, correct_upd_pc.v correct_eval_pc.v correct_upd_pc_incr.v correct_eval_reg.v  correct_eval_flag.v correct_upd_flag.v correct_eval_mrs_regions.v correct_get_addr_ofs.v correct_get_dst.v correct_get_immediate.v correct_is_well_chunk_bool.v correct_get_block_ptr.v correct_get_block_size.v correct_get_start_addr.v correct_get_block_perm.v correct_get_add.v correct_get_sub.v correct_upd_reg.v correct_reg64_to_reg32.v correct_get_opcode_alu64.v correct_get_opcode_branch.v correct_step_opcode_alu64.v correct_step_opcode_branch.v)

# correct_check_mem_aux.v  correct_load_mem.v

CLIGHTLOGICDIR =  $(addprefix proof/, clight_exec.v CommonLib.v Clightlogic.v MatchState.v CorrectRel.v CommonLemma.v CommonLemmaNat.v)


clightlogic:
	@echo $@
#	rm -f proof/*.vo
	$(COQMAKEFILE) -f _CoqProject $(CLIGHTLOGICDIR) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefilePrf
	make -f CoqMakefilePrf

simulation:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(PROOF) COQEXTRAFLAGS = '-w all,-extraction'  -o CoqMakefilePrf
	make -f CoqMakefilePrf

GITDIR=/home/shyuan/GitLab/rbpf-dx

gitpush:
	@echo $@
	cp src/*.v $(GITDIR)/src
	cp src/*.c $(GITDIR)/src
	cp comm/*.v $(GITDIR)/comm
	cp comm/*.md $(GITDIR)/comm
	cp model/*.v $(GITDIR)/model
	cp model/*.md $(GITDIR)/model
	cp monadicmodel/*.v $(GITDIR)/monadicmodel
	cp monadicmodel/*.md $(GITDIR)/monadicmodel
	cp equivalence/*.v $(GITDIR)/equivalence
	cp equivalence/*.md $(GITDIR)/equivalence
	cp isolation/*.v $(GITDIR)/isolation
	cp isolation/*.md $(GITDIR)/isolation
	cp simulation/*.v $(GITDIR)/simulation
	cp benchmark/*.v $(GITDIR)/benchmark
	cp benchmark/*.c $(GITDIR)/benchmark
	cp benchmark/*.h $(GITDIR)/benchmark
	cp benchmark/*.md $(GITDIR)/benchmark
	cp benchmark/proof/*.v $(GITDIR)/benchmark/proof
	cp clight/*.v $(GITDIR)/clight
	cp clight/*.c $(GITDIR)/clight
	cp clight/*.h $(GITDIR)/clight
	cp proof/*.v $(GITDIR)/proof
	cp proof/*.md $(GITDIR)/proof
	cp repatch/*.c $(GITDIR)/repatch
	cp Makefile $(GITDIR)
	cp Makefile.config $(GITDIR)
	cp _CoqProject $(GITDIR)
	cp compcertsrc-I $(GITDIR)
	cp compcertcprinter-cmx-args $(GITDIR)
	cp *.md $(GITDIR)

gitpull:
	@echo $@
	cp $(GITDIR)/src/*.v ./src
	cp $(GITDIR)/src/*.c ./src
	cp $(GITDIR)/comm/*.v ./comm
	cp $(GITDIR)/comm/*.md ./comm
	cp $(GITDIR)/model/*.v ./model
	cp $(GITDIR)/model/*.md ./model
	cp $(GITDIR)/monadicmodel/*.v ./monadicmodel
	cp $(GITDIR)/monadicmodel/*.md ./monadicmodel
	cp $(GITDIR)/equivalence/*.v ./equivalence
	cp $(GITDIR)/equivalence/*.md ./equivalence
	cp $(GITDIR)/isolation/*.v ./isolation
	cp $(GITDIR)/isolation/*.md ./isolation
	cp $(GITDIR)/simulation/*.v ./simulation
	cp $(GITDIR)/benchmark/*.v ./benchmark
	cp $(GITDIR)/benchmark/*.c ./benchmark
	cp $(GITDIR)/benchmark/*.h ./benchmark
	cp $(GITDIR)/benchmark/*.md ./benchmark
	cp $(GITDIR)/benchmark/proof/*.v ./benchmark/proof
	cp $(GITDIR)/clight/*.v ./clight
	cp $(GITDIR)/clight/*.c ./clight
	cp $(GITDIR)/clight/*.h ./clight
	cp $(GITDIR)/proof/*.v ./proof
	cp $(GITDIR)/proof/*.md ./proof
	cp $(GITDIR)/repatch/*.c ./repatch
	cp $(GITDIR)/Makefile .
	cp $(GITDIR)/Makefile.config .
	cp $(GITDIR)/_CoqProject .
	cp $(GITDIR)/compcertsrc-I .
	cp $(GITDIR)/compcertcprinter-cmx-args .
	cp $(GITDIR)/*.md .

clean :
	@echo $@
	make -f CoqMakefile clean
	make -f CoqMakefilePrf clean
	find . -name "*\.vo" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;
	find . -name "*\.crashcoqide" -exec rm {} \;


# We want to keep the .cmi that were built as we go
.SECONDARY:

.PHONY: all test bench bench_clight comm model monadicmodel isolation equivalence compile extract repatch clightmodel proof simulation clean
