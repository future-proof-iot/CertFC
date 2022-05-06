
# Build world: opam

_NB: you may need to add `sudo` everywhere_

```shell
# assume your ubuntu is named `cav`
# current folder: /home/cav/CertrBPF
# install the basic tool
apt-get update && apt-get install -y software-properties-common

# install gcc 9.4.0
apt install build-essential

# install gcc lib
apt-get install gcc-multilib

# install llvm
apt-get install -y llvm
apt-get install clang

# install pip3 and pyelftools
apt install python3-pip python3-serial
pip3 install pyelftools

# install opam
add-apt-repository ppa:avsm/ppa
apt update
apt install opam

# install ocaml/coq/compcert etc by opam
opam init
# install ocaml
opam switch create bpf ocaml.4.11.1

eval $(opam env)

opam switch list
#   switch  compiler      description
->  bpf     ocaml.4.11.1  bpf

# install coq, compcert-32, etc. NB we need to keep the build directory of compcert-32 by `-b`
opam repository add coq-released https://coq.inria.fr/opam/released

# install coq and coqide
opam install coq.8.13.2 coqide.8.13.2 coq-elpi.1.11.0
opam install -b coq-compcert-32.3.9
opam install coq-vst-32.2.8

# install coq2html
git clone https://github.com/xavierleroy/coq2html.git
cd coq2html
make coq2html

# set path variables
apt-get install vim
# 1) find . -name ".opam" -type d
#  ==> ./home/cav/.opam
# 2); adding the line: export PATH=$PATH:/home/cav/.opam/bpf/bin:/home/cav/CertrBPF/coq2html
vim /home/cav/.bashrc
source /home/cav/.bashrc
```

# Build dx
```shell
# current folder: /home/cav/CertrBPF
# install dx
cd /home/
mkdir CertrBPF
cd CertrBPF/
git clone --branch compcert-3.9 https://gitlab.univ-lille.fr/samuel.hym/dx.git
cd dx
# modify the _CoqProject (adding the second line):
# -R src dx
# -R /home/cav/.opam/bpf/lib/coq-variant/compcert32/compcert compcert
# -R tests dx.tests
vim _CoqProject

# modify the Makefile
# COQEXTROPTS := $(shell $(SED) 's/-[RQ]  */&..\//g' _CoqProject) -w all,-extraction
# ==>
# COQEXTROPTS := -R ../src dx -R $(COMPCERTSRCDIR) compcert -R ../tests dx.tests -w all,-extraction
vim Makefile

# add a file named: compcertsrc-I
# Its contents (removing all #):
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/x86
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/backend
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/debug
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/common
# -I
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cfrontend
vim compcertsrc-I

# adding the following string (removing #) the file `compcertcprinter-cmi`: 
# /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Datatypes.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Nat.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinNums.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinPosDef.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinPos.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zpower.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinNat.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinInt.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/ZArith_dec.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/List0.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Coqlib.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zbits.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Readconfig.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Responsefile.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Commandline.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver/Configuration.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Archi.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Integers.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zaux.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/SpecFloat.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zbool.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Round.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/FLT.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Bracket.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Bool.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Binary.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/IEEE754_extra.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Bits.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Floats.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/String0.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/EquivDec.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Maps.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Errors.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/AST.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Values.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Ctypes.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Znumtheory.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Memtype.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/PeanoNat.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Memdata.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Memory.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Cop.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Csyntax.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Camlcoq.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver/Version.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Diagnostics.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Machine.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Env.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Cprint.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Cutil.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver/Clflags.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/common/Sections.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Initializers.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BoolEqual.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Op.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Machregs.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/backend/Machregsnames.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/x86/Machregsaux.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Ceval.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/x86/CBuiltins.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/ExtendedAsm.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/debug/Debug.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Ctyping.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/backend/AisAnnot.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cfrontend/C2C.cmi /home/cav/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cfrontend/PrintCsyntax.cmi 

vim compcertcprinter-cmi

./configure ...
./configure --compcertdir=/home/cav/.opam/bpf/lib/coq-variant/compcert32/compcert --install-compcert-printer --cprinterdir=/home/cav/.opam/bpf/lib/coq/user-contrib/dx/extr
make; make install
# stop and return the following infomation, but it works 
# /bin/sh: 1: tools/modorder: not found
# install: missing destination file operand after '/home/cav/.opam/bpf/lib/coq/user-contrib/dx/extr/compcertcprinter'
# Try 'install --help' for more information.
# make: *** [Makefile:199: install] Error 1

# copy two files
cp cprinter-inc-args /home/cav/.opam/bpf/lib/coq/user-contrib/dx/
cp cprinter-link-args /home/cav/.opam/bpf/lib/coq/user-contrib/dx/
```
# Build CertrBPF
```shell
# current folder: /home/cav/CertrBPF/dx
# install CertrBPF
cd ..
git clone --branch CAV22-AE https://gitlab.inria.fr/syuan/rbpf-dx.git
cd rbpf-dx

# modify the file `_CoqProject`:
# -R /home/shyuan/.opam/4.11.1/lib/coq-variant/compcert32/compcert compcert
# ===>
# -R /home/cav/.opam/bpf/lib/coq-variant/compcert32/compcert compcert
vim _CoqProject

# modify the file `Makefile.config` and `verifier/Makefile.config`:
# OPAMPREFIX := /home/shyuan/.opam/4.11.1
# ===>
# OPAMPREFIX := /home/cav/.opam/bpf
vim Makefile.config
vim verifier/Makefile.config

cp /home/cav/CertrBPF/dx/compcertsrc-I .

make all
```
# Test CertrBPF 
```shell
# current folder: /home/cav/CertrBPF/rbpf-dx
# Here, we only test the native board (*You could reproduce the same result in the paper if you have the same physical boards: Nordic nRF52840 development kit, the Espressif WROOM-32 board, and the Sipeed Longan Nano GD32VF103CBT6 development board*)

# test bench_bpf_coq_incr
# compile CertBPF
make -C benchmark_data/bench_bpf_coq_incr/bpf
make -C benchmark_data/bench_bpf_coq_incr
# run on a native port using CertBPF
make -C benchmark_data/bench_bpf_coq_incr term
# complie original rBPF: Vanilla-rBPF
make -C benchmark_data/bench_bpf_coq_incr BPF_COQ=0 BPF_USE_JUMPTABLE=0
make -C benchmark_data/bench_bpf_coq_incr BPF_COQ=0 BPF_USE_JUMPTABLE=0 term

# test bench_bpf_coq_unit
# compile CertBPF
make -C benchmark_data/bench_bpf_coq_unit
make -C benchmark_data/bench_bpf_coq_unit term
# complie original rBPF: Vanilla-rBPF
make -C benchmark_data/bench_bpf_coq_unit BPF_COQ=0 BPF_USE_JUMPTABLE=0
make -C benchmark_data/bench_bpf_coq_unit BPF_COQ=0 BPF_USE_JUMPTABLE=0 term
```

Please don't hesitate to contact [me](https://shenghaoyuan.github.io/)
