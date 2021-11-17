##########################################################################
#  This file is part of dx, a tool to derive C from monadic Gallina.     #
#                                                                        #
#  Copyright (C) 2021 Université de Lille & CNRS                         #
#                                                                        #
#  This program is free software; you can redistribute it and/or modify  #
#  it under the terms of the GNU General Public License as published by  #
#  the Free Software Foundation; either version 2 of the License, or     #
#  (at your option) any later version.                                   #
#                                                                        #
#  This program is distributed in the hope that it will be useful,       #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU General Public License for more details.                          #
##########################################################################

include Makefile.config

SED := sed
CAT := cat
AWK := awk
COQC := coqc
COQDEP := coqdep
OCAMLOPT := ocamlopt

# Disable warnings on notations (that are coming from the standard
# library)
COQPROJOPTS := $(shell $(CAT) _CoqProject)
COQDEPOPTS := $(COQPROJOPTS)
COQCOPTS := $(COQPROJOPTS) -w all,-notation
COQEXTROPTS := $(shell $(SED) 's/-[RQ]  */&..\//g' _CoqProject) -w all,-extraction

OCAMLINCS := -I extr -I src

COQSOURCES := $(wildcard src/*.v src/*/*.v)
ifeq ($(strip $(CPRINTERDIR)),)
COQSOURCES := $(filter-out src/DumpAsC.v,$(COQSOURCES))
endif
COQTARGETS := $(patsubst %.v, %.vo, $(COQSOURCES))

INSTALLDEPS := $(COQTARGETS)

EXTRACTEDMODULES := ResultMonad DXModule
EXTRACTEDOCAMLFILES := $(addprefix extr/,$(addsuffix .ml,$(EXTRACTEDMODULES)) \
                                         $(addsuffix .mli,$(EXTRACTEDMODULES)))
EXTRACTEDMODULESSRC := $(addprefix src/,$(addsuffix .vo,$(EXTRACTEDMODULES)))

INSTALLEDOCAMLFILES := $(addprefix extr/,$(addsuffix .cmi,$(EXTRACTEDMODULES)) \
                                         $(addsuffix .cmx,$(EXTRACTEDMODULES)) \
                                         $(addsuffix .o,$(EXTRACTEDMODULES)))
INSTALLEDOCAMLFILES += src/DumpAsC.cmi src/DumpAsC.cmx src/DumpAsC.o

ifneq ($(strip $(CPRINTERDIR)),)
INSTALLDEPS += $(INSTALLEDOCAMLFILES) cprinter-inc-args cprinter-link-args
ifeq ($(INSTALLCOMPCERTCPRINTER),true)
INSTALLDEPS += compcertcprinter.cmxa compcertcprinter.a
endif
endif


all: $(INSTALLDEPS)

test: tests/generated.c

.depend.coq: $(wildcard */*.v */*/*.v)
	$(COQDEP) $(COQDEPOPTS) $^ > $@

-include .depend.coq

ifneq (,$(findstring grouped-target,$(.FEATURES)))

extr/Extr.vo $(EXTRACTEDOCAMLFILES) &: extr/Extr.v $(EXTRACTEDMODULESSRC)
	cd extr/ && $(COQC) $(COQEXTROPTS) Extr.v

tests/ExtrMain.vo tests/TestMain.ml tests/TestMain.mli &: tests/ExtrMain.v src/DumpAsC.vo tests/TestMain.vo
	cd tests/ && $(COQC) $(COQEXTROPTS) ExtrMain.v

compcertcprinter.cmxa compcertcprinter.a &: compcertcprinter-cmx-args compcertsrc-I
	$(OCAMLOPT) -args compcertsrc-I -a -args $< -o $@

src/DumpAsC.cmi src/DumpAsC.cmx src/DumpAsC.o &: src/DumpAsC.ml compcertsrc-I extr/ResultMonad.cmi extr/DXModule.cmi
	$(OCAMLOPT) -args compcertsrc-I -I extr -c $<

else

extr/Extr.vo $(EXTRACTEDOCAMLFILES): extr/Extr.v $(EXTRACTEDMODULESSRC)
	cd extr/ && $(COQC) $(COQEXTROPTS) Extr.v

tests/ExtrMain.vo tests/TestMain.ml tests/TestMain.mli: tests/ExtrMain.v src/DumpAsC.vo tests/TestMain.vo
	cd tests/ && $(COQC) $(COQEXTROPTS) ExtrMain.v

compcertcprinter.cmxa compcertcprinter.a: compcertcprinter-cmx-args compcertsrc-I
	$(OCAMLOPT) -args compcertsrc-I -a -args $< -o $@

src/DumpAsC.cmi src/DumpAsC.cmx src/DumpAsC.o: src/DumpAsC.ml compcertsrc-I extr/ResultMonad.cmi extr/DXModule.cmi
	$(OCAMLOPT) -args compcertsrc-I -I extr -c $<

endif

compcertsrc-I:
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
	            }' > $@

compcertcprinter-cmx-args:
	$(COMPCERTSRCDIR)/tools/modorder $(COMPCERTSRCDIR)/.depend.extr cfrontend/PrintCsyntax.cmx | \
	    $(AWK) 'BEGIN { RS=" " } /cmx/ { gsub(".*/","") ; print }' > $@

compcertcprinter-cmi:
	$(COMPCERTSRCDIR)/tools/modorder $(COMPCERTSRCDIR)/.depend.extr cfrontend/PrintCsyntax.cmx | \
	    $(AWK) 'BEGIN { RS=" " ; ORS=" " } ;                                                     \
	            /cmx/ { gsub("cmx$$","cmi") ; print "$(COMPCERTSRCDIR)/" $$0 }' > $@

ifneq ($(strip $(CPRINTERDIR)),)
cprinter-inc-args: compcertsrc-I
	printf -- '-I\n%s\n' "$(CPRINTERDIR)" > $@
ifeq ($(INSTALLCOMPCERTCPRINTER),true)
	printf -- '-I\n%s\n' "$(CPRINTERDIR)/compcertcprinter" >> $@
else
	cat compcertsrc-I >> $@
endif

cprinter-link-args: compcertcprinter-cmx-args
	printf 'str.cmxa\nunix.cmxa\n' >> $@
ifeq ($(INSTALLCOMPCERTCPRINTER),true)
	printf 'compcertcprinter.cmxa\n' >> $@
else
	cat compcertcprinter-cmx-args >> $@
endif
	printf 'ResultMonad.cmx\nDXModule.cmx\nDumpAsC.cmx\n' >> $@

INSTALLDEPS += compcertcprinter-cmi
endif

tests/%.cmx: OCAMLINCS+=-I tests
tests/%.o: OCAMLINCS+=-I tests

tests/main: extr/ResultMonad.cmx extr/DXModule.cmx src/DumpAsC.cmx tests/TestMain.cmx \
	    extr/ResultMonad.o   extr/DXModule.o   src/DumpAsC.o   tests/TestMain.o   \
	    compcertsrc-I compcertcprinter.cmxa compcertcprinter.a
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(filter %.cmx,$^) -o $@

ifneq ($(strip $(CPRINTERDIR)),)
tests/main-after-install: tests/TestMain.cmx tests/TestMain.o
	$(OCAMLOPT) -args $(CPRINTERDIR)/cprinter-inc-args -args $(CPRINTERDIR)/cprinter-link-args $< -o $@
endif

tests/generated.c: tests/main tests/compcert.ini
	cd tests && ./main
#	diff -u tests/expected.c $@

tests/compcert.ini:
	ln -sf $(COMPCERTSRCDIR)/compcert.ini $@

## Implicit rules

%.vo: %.v
	$(COQC) $(COQCOPTS) $<

%.cmi: %.mli compcertsrc-I
	$(OCAMLOPT) -args compcertsrc-I $(OCAMLINCS) $<

ifneq (,$(findstring grouped-target,$(.FEATURES)))
%.cmx %.o &: %.ml %.cmi compcertsrc-I
	$(OCAMLOPT) -args compcertsrc-I $(OCAMLINCS) -c $<
else
%.cmx %.o: %.ml %.cmi compcertsrc-I
	$(OCAMLOPT) -args compcertsrc-I $(OCAMLINCS) -c $<
endif

INSTALL := install
INSTALL_DATA := $(INSTALL) -m 0644

install: $(INSTALLDEPS)
	$(INSTALL) -d $(DESTDIR)$(COQDEVDIR)
	$(INSTALL_DATA) src/*.vo $(DESTDIR)$(COQDEVDIR)
	$(INSTALL) -d $(DESTDIR)$(COQDEVDIR)/Type
	$(INSTALL_DATA) src/Type/*.vo $(DESTDIR)$(COQDEVDIR)/Type/

ifneq ($(strip $(CPRINTERDIR)),)
	$(INSTALL) -d $(DESTDIR)$(CPRINTERDIR)
	$(INSTALL_DATA) $(INSTALLEDOCAMLFILES) $(DESTDIR)$(CPRINTERDIR)
	$(INSTALL_DATA) cprinter-inc-args cprinter-link-args $(DESTDIR)$(CPRINTERDIR)
ifeq ($(INSTALLCOMPCERTCPRINTER),true)
	$(INSTALL) -d $(DESTDIR)$(CPRINTERDIR)/compcertcprinter
	$(INSTALL_DATA) doc/Readme-for-installed-CompCert-files $(DESTDIR)$(CPRINTERDIR)/compcertcprinter/README
	$(INSTALL_DATA) compcertcprinter.cmxa compcertcprinter.a $(DESTDIR)$(CPRINTERDIR)/compcertcprinter
	$(INSTALL_DATA) `cat compcertcprinter-cmi` $(DESTDIR)$(CPRINTERDIR)/compcertcprinter
	cd $(COMPCERTSRCDIR) && \
	    $(INSTALL_DATA) `tools/modorder .depend.extr cfrontend/PrintCsyntax.cmx` \
	         $(DESTDIR)$(CPRINTERDIR)/compcertcprinter
	$(INSTALL_DATA) $(COMPCERTSRCDIR)/compcert.ini $(DESTDIR)$(CPRINTERDIR)/compcertcprinter
endif
endif

ci-dependencies:
	opam init -ya
	eval $$(opam env) ;                                                      \
	opam repository -y add coq-released https://coq.inria.fr/opam/released ; \
	opam install -y coq coq-elpi ;                                           \
	opam install -y --deps-only coq-compcert ;                               \
	opam install -y -b coq-compcert

clean:
	rm -f */*.glob */*.vo */*.vok */*.vos */.*.aux */*/*.glob */*/*.vo */*/*.vok */*/*.vos */*/.*.aux
	rm -f extr/*.ml extr/*.mli tests/*.ml tests/*.mli
	rm -f */*.cmi */*.cmx */*.o
	rm -f tests/compcert.ini tests/main tests/generated.c tests/main-after-install
	rm -f compcertsrc-I compcertcprinter-cmx-args compcertcprinter-cmi
	rm -f cprinter-inc-args cprinter-link-args
	rm -f compcertcprinter.cmxa compcertcprinter.a
	rm -f .depend.coq
	rm -f .lia.cache

# We want to keep the .cmi that were built as we go
.SECONDARY:

.PHONY: all test clean install ci-dependencies
