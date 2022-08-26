include Makefile.config

SED := sed
CAT := cat
AWK := awk
COQC := coqc
#COQDEP := coqdep
OCAMLOPT := ocamlopt
COQMAKEFILE := coq_makefile
CP := cp
MV := mv

CC=gcc
ARMCC=arm-none-eabi-gcc
ARMDUMP=arm-none-eabi-objdump
OFLAGS=-Os
CLIGHTGEN=clightgen
CLIGHTGEN32=$(CLIGHTGEN32DIR)/clightgen

THIS_FILE := $(lastword $(MAKEFILE_LIST))

COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

OCAMLINCS := -I extr # -I src

DIRS := comm dxcomm model verifier isolation monadicmodel dxmodel clight clightlogic simulation equivalence

COQINCLUDES := INSTALLDEFAULTROOT = comm "\n"
COQINCLUDES += $(foreach d, $(DIRS),-R $(d) bpf.$(d) "\n")
COQINCLUDES +=-R $(COMPCERTDIR) compcert

COQDEP="$(COQBIN)coqdep" -exclude-dir aarch64 -exclude-dir x86_64 -exclude-dir riscV -exclude-dir powerpc -exclude-dir x86_32 $(COQINCLUDES)

#COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)

proof: $(FILES:.v=.vo)

%.vo: %.v
	@rm -f html/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/glob/$(*F).glob $*.v

all:
	@echo $@
	@$(MAKE) comm
	@$(MAKE) dxcomm
	@$(MAKE) model
	@$(MAKE) verifier
	@$(MAKE) isolation
	@$(MAKE) monadicmodel
	@$(MAKE) compile
	@$(MAKE) repatch
	@$(MAKE) clightmodel
	@$(MAKE) clightlogic
	@$(MAKE) simulation
	@$(MAKE) equivalence
	@$(MAKE) dxverifier
	@$(MAKE) document

COMM= Flag.v LemmaNat.v LemmaInt.v ListAsArray.v rBPFAST.v rBPFMemType.v rBPFValues.v MemRegion.v Regs.v BinrBPF.v \
   State.v Monad.v rBPFMonadOp.v
   
DXCOMM= InfComp.v GenMatchable.v \
   CoqIntegers.v DxIntegers.v DxValues.v DxListAsArray.v DxBinrBPF.v DxNat.v
   
MODEL= Syntax.v Decode.v Semantics.v Encode.v PrintrBPF.v
   
VERIFIER= comm/state.v comm/monad.v \
   synthesismodel/opcode_synthesis.v synthesismodel/verifier_synthesis.v \
   dxmodel/Dxopcode.v dxmodel/Dxstate.v dxmodel/Dxmonad.v dxmodel/Dxverifier.v dxmodel/verifier_dx.v dxmodel/verifier_TestMain.v dxmodel/verifier_ExtrMain.v
   
DXVERIFIER= clightmodel/verifier.v \
   simulation/VerifierSimulation.v simulation/VerifierRel.v \
   simulation/correct_bpf_verifier_eval_ins.v simulation/correct_bpf_verifier_eval_ins_len.v simulation/correct_is_dst_R0.v simulation/correct_is_well_dst.v \
   simulation/correct_is_well_src.v simulation/correct_is_well_jump.v simulation/correct_is_not_div_by_zero.v simulation/correct_is_not_div_by_zero64.v \
   simulation/correct_is_shift_range.v simulation/correct_is_shift_range64.v simulation/correct_bpf_verifier_get_opcode.v simulation/correct_bpf_verifier_get_offset.v \
   simulation/correct_bpf_verifier_opcode_alu32_imm.v simulation/correct_bpf_verifier_opcode_alu32_reg.v simulation/correct_bpf_verifier_opcode_alu64_imm.v \
   simulation/correct_bpf_verifier_opcode_alu64_reg.v simulation/correct_bpf_verifier_opcode_branch_imm.v simulation/correct_bpf_verifier_opcode_branch_reg.v \
   simulation/correct_bpf_verifier_opcode_load_imm.v simulation/correct_bpf_verifier_opcode_load_reg.v simulation/correct_bpf_verifier_opcode_store_imm.v \
   simulation/correct_bpf_verifier_opcode_store_reg.v simulation/correct_bpf_verifier_aux2.v simulation/correct_bpf_verifier_aux.v simulation/correct_bpf_verifier.v \
   property/equivalence.v property/invariant.v

MONADIC= Opcode.v rBPFInterpreter.v
   
DXMODEL= DxAST.v DxFlag.v DxOpcode.v IdentDef.v DxMemType.v DxMemRegion.v DxRegs.v \
    DxState.v DxMonad.v DxInstructions.v \
    Tests.v TestMain.v ExtrMain.v

CLIGHTLOGIC= clight_exec.v Clightlogic.v \
    CommonLib.v CommonLemma.v CorrectRel.v CommonLemmaNat.v

QUIV = equivalence1.v equivalence2.v

ISOLATION=CommonISOLib.v AlignChunk.v VerifierOpcode.v \
    RegsInv.v MemInv.v VerifierInv.v CheckMem.v StateInv.v \
    IsolationLemma.v Isolation1.v Isolation2.v

SIMULATION=MatchState.v InterpreterRel.v \
    correct_eval_pc.v correct_upd_pc.v correct_upd_pc_incr.v correct_eval_reg.v correct_upd_reg.v correct_eval_flag.v correct_upd_flag.v \
    correct_eval_mrs_num.v correct_eval_mrs_regions.v correct_load_mem.v correct_store_mem_reg.v correct_store_mem_imm.v \
    correct_eval_ins_len.v correct_eval_ins.v correct_cmp_ptr32_nullM.v correct_get_dst.v correct_get_src.v correct_get_mem_region.v \
    correct__bpf_get_call.v correct_exec_function.v  \
    correct_reg64_to_reg32.v correct_get_offset.v correct_get_immediate.v correct_eval_immediate.v correct_get_src64.v correct_get_src32.v \
    correct_get_opcode_ins.v correct_get_opcode_alu64.v correct_get_opcode_alu32.v correct_get_opcode_branch.v correct_get_opcode_mem_ld_imm.v \
    correct_get_opcode_mem_ld_reg.v correct_get_opcode_mem_st_imm.v correct_get_opcode_mem_st_reg.v correct_get_opcode.v \
    correct_get_add.v correct_get_sub.v correct_get_addr_ofs.v correct_get_start_addr.v correct_get_block_size.v correct_get_block_perm.v \
    correct_is_well_chunk_bool.v correct_check_mem_aux2.v correct_check_mem_aux.v correct_check_mem.v \
    correct_step_opcode_alu64.v correct_step_opcode_alu32.v correct_step_opcode_branch.v \
    correct_step_opcode_mem_ld_imm.v correct_step_opcode_mem_ld_reg.v correct_step_opcode_mem_st_reg.v correct_step_opcode_mem_st_imm.v \
    correct_step.v correct_bpf_interpreter_aux.v correct_bpf_interpreter.v


COQCOMM = $(addprefix comm/, $(COMM))
COQDXCOMM = $(addprefix dxcomm/, $(DXCOMM))
COQMODEL =  $(addprefix model/, $(MODEL))
COQVERIFIER =  $(addprefix verifier/,  $(VERIFIER))
COQEMONADIC =  $(addprefix monadicmodel/, $(MONADIC))
COQDXMODEL =  $(addprefix dxmodel/, $(DXMODEL))
CLIGHTLOGICDIR =  $(addprefix clightlogic/, $(CLIGHTLOGIC))
PROOF = $(addprefix simulation/, $(SIMULATION))
COQEQUIV =  $(addprefix equivalence/, $(QUIV))
COQISOLATION = $(addprefix isolation/, $(ISOLATION))
COQDXVERIFIER= $(addprefix verifier/, $(DXVERIFIER))

FILES=$(COQCOMM) $(COQDXCOMM) $(COQMODEL) $(COQVERIFIER) $(COQEMONADIC) $(COQDXMODEL) \
  $(CLIGHTLOGICDIR) $(PROOF) $(COQEQUIV) $(COQISOLATION) $(COQDXVERIFIER)

depend: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

comm:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQCOMM) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

dxcomm:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQDXCOMM) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

verifier:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQVERIFIER) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	$(CP) verifier_TestMain.ml verifier/dxmodel
	$(CP) verifier_TestMain.mli verifier/dxmodel
	
dxverifier:
	@echo $@
	cd verifier && $(MAKE) verifier-all
	$(COQMAKEFILE) -f _CoqProject $(COQDXVERIFIER) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

model:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQMODEL) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

monadicmodel:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQEMONADIC) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

isolation:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQISOLATION) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

equivalence:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQEQUIV) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

compile:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQDXMODEL) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	$(CP) TestMain.ml dxmodel
	$(CP) TestMain.mli dxmodel
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
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I dxmodel dxmodel/TestMain.mli	
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I dxmodel -c dxmodel/TestMain.ml
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.cmxa
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.a
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(DXDIR)/ResultMonad.cmx $(DXDIR)/DXModule.cmx $(DXDIR)/DumpAsC.cmx dxmodel/TestMain.cmx -o dxmodel/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini dxmodel/compcert.ini
	cd dxmodel && ./main

repatch:
	@echo $@
	$(MV) dxmodel/generated.c repatch
	cd repatch && $(CC) -o repatch1 repatch1.c && ./repatch1 && $(CC) -o repatch2 repatch2.c && ./repatch2 && $(CC) -o repatch3 repatch3.c && ./repatch3 && $(CC) -o repatch4 repatch4.c && ./repatch4
	$(MV) repatch/interpreter.c clight

clightmodel:
	@echo $@
	cd clight && $(CC) -o $@ $(OFLAGS) fletcher32_bpf_test.c interpreter.c && ./$@
	cd clight && $(CLIGHTGEN32) interpreter.c
	$(COQMAKEFILE) -f _CoqProject clight/interpreter.v $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

clightlogic:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(CLIGHTLOGICDIR) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

simulation:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(PROOF) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

DOCFLAG := -external https://compcert.org/doc/html compcert -base bpf -short-names 
document:
	@echo $@
	mkdir -p html
	mkdir -p html/glob
	cp clight/*.glob html/glob
	cp clightlogic/*.glob html/glob
	cp comm/*.glob html/glob
	cp dxcomm/*.glob html/glob
	cp dxmodel/*.glob html/glob
	cp equivalence/*.glob html/glob
	cp model/*.glob html/glob
	cp monadicmodel/*.glob html/glob
	cp simulation/*.glob html/glob
	cp isolation/*.glob html/glob
	cp verifier/clightmodel/*.glob html/glob
	cp verifier/comm/*.glob html/glob
	cp verifier/dxmodel/*.glob html/glob
	cp verifier/property/*.glob html/glob
	cp verifier/simulation/*.glob html/glob
	cp verifier/synthesismodel/*.glob html/glob
	coq2html $(DOCFLAG) -d html html/glob/*.glob clight/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob clightlogic/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob comm/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob dxcomm/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob dxmodel/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob equivalence/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob model/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob monadicmodel/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob simulation/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob isolation/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob verifier/clightmodel/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob verifier/comm/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob verifier/dxmodel/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob verifier/property/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob verifier/simulation/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob verifier/synthesismodel/*.v

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

GITDIR=/home/shyuan/GitHub/CertFC

gitpush:
	@echo $@
	cp clight/*.v $(GITDIR)/clight
	cp clight/*.c $(GITDIR)/clight
	cp clight/*.h $(GITDIR)/clight
	cp clightlogic/*.v $(GITDIR)/clightlogic
	cp clightlogic/*.md $(GITDIR)/clightlogic
	cp comm/*.v $(GITDIR)/comm
	cp comm/*.md $(GITDIR)/comm
	cp dxcomm/*.v $(GITDIR)/dxcomm
	cp dxmodel/*.v $(GITDIR)/dxmodel
	cp equivalence/*.v $(GITDIR)/equivalence
	cp equivalence/*.md $(GITDIR)/equivalence
	cp model/*.v $(GITDIR)/model
	cp model/*.md $(GITDIR)/model
	cp monadicmodel/*.v $(GITDIR)/monadicmodel
	cp monadicmodel/*.md $(GITDIR)/monadicmodel
	cp repatch/*.c $(GITDIR)/repatch
	cp simulation/*.v $(GITDIR)/simulation
	cp isolation/*.v $(GITDIR)/isolation
	cp isolation/*.md $(GITDIR)/isolation
	cp Makefile $(GITDIR)
	cp *.md $(GITDIR)
	cp LICENSE $(GITDIR)
	cp configure $(GITDIR)
	cp verifier/clightmodel/*.h $(GITDIR)/verifier/clightmodel
	cp verifier/clightmodel/*.c $(GITDIR)/verifier/clightmodel
	cp verifier/clightmodel/*.v $(GITDIR)/verifier/clightmodel
	cp verifier/comm/*.v $(GITDIR)/verifier/comm
	cp verifier/dxmodel/*.v $(GITDIR)/verifier/dxmodel
	cp verifier/property/*.v $(GITDIR)/verifier/property
	cp verifier/repatch/*.c $(GITDIR)/verifier/repatch
	cp verifier/simulation/*.v $(GITDIR)/verifier/simulation
	cp verifier/synthesismodel/*.v $(GITDIR)/verifier/synthesismodel
	cp verifier/Makefile $(GITDIR)/verifier
	cp verifier/*.md $(GITDIR)/verifier

gitpull:
	@echo $@
	cp $(GITDIR)/dxmodel/*.v ./dxmodel
	cp $(GITDIR)/dxmodel/*.c ./dxmodel
	cp $(GITDIR)/comm/*.v ./comm
	cp $(GITDIR)/comm/*.md ./comm
	cp $(GITDIR)/dxcomm/*.v ./dxcomm
	cp $(GITDIR)/model/*.v ./model
	cp $(GITDIR)/model/*.md ./model
	cp $(GITDIR)/monadicmodel/*.v ./monadicmodel
	cp $(GITDIR)/monadicmodel/*.md ./monadicmodel
	cp $(GITDIR)/equivalence/*.v ./equivalence
	cp $(GITDIR)/equivalence/*.md ./equivalence
	cp $(GITDIR)/isolation/*.v ./isolation
	cp $(GITDIR)/isolation/*.md ./isolation
	cp $(GITDIR)/simulation/*.v ./simulation
	cp $(GITDIR)/clight/*.v ./clight
	cp $(GITDIR)/clight/*.c ./clight
	cp $(GITDIR)/clight/*.h ./clight
	cp $(GITDIR)/clightlogic/*.v ./clightlogic
	cp $(GITDIR)/clightlogic/*.md ./clightlogic
	cp $(GITDIR)/repatch/*.c ./repatch
	cp $(GITDIR)/Makefile .
	cp $(GITDIR)/*.md .
	cp $(GITDIR)/LICENSE .
	cp $(GITDIR)/configure .
	cp $(GITDIR)/verifier/Makefile ./verifier
	cp $(GITDIR)/verifier/*.md ./verifier
	cp $(GITDIR)/verifier/clightmodel/*.h ./verifier/clightmodel
	cp $(GITDIR)/verifier/clightmodel/*.c ./verifier/clightmodel
	cp $(GITDIR)/verifier/clightmodel/*.v ./verifier/clightmodel
	cp $(GITDIR)/verifier/comm/*.v ./verifier/comm
	cp $(GITDIR)/verifier/dxmodel/*.v ./verifier/dxmodel
	cp $(GITDIR)/verifier/property/*.v ./verifier/property
	cp $(GITDIR)/verifier/repatch/*.c ./verifier/repatch
	cp $(GITDIR)/verifier/synthesismodel/*.v ./verifier/synthesismodel
	cp $(GITDIR)/verifier/simulation/*.v ./verifier/simulation

clean :
	@echo $@
	make -f CoqMakefile clean
	find . -name "*\.vo" -exec rm {} \;
	find . -name "*\.vok" -exec rm {} \;
	find . -name "*\.vos" -exec rm {} \;
	find . -name "*\.glob" -exec rm {} \;
	find . -name "*\.aux" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;
	find . -name "*\.crashcoqide" -exec rm {} \;


# We want to keep the .cmi that were built as we go
.SECONDARY:

.PHONY: all test comm dxcomm verifier dxverifier model monadicmodel isolation equivalence compile extract repatch clightmodel clightlogic simulation clean
