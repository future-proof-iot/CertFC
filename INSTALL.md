
# Build world: opam
```shell
# who: root@8d187e7952ec:/#
# install the basic tool
apt-get update && apt-get install -y software-properties-common

# install gcc 9.4.0
apt install build-essential

# install gcc lib
apt-get install gcc-multilib

# install llvm
apt-get install -y llvm

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

# install coq and coqide
opam install coq=8.13.2
opam install coqide=8.13.2

# install compcert-32, NB we need to keep the build directory
opam repository add coq-released https://coq.inria.fr/opam/released
opam install -b coq-compcert-32.3.9

# install coq-elpi
opam install coq-elpi=1.11.0

# install coq-vst-32
opam install coq-vst-32=2.8

# set path variables
apt-get install vim
# 1) find . -name ".opam" -type d
#  ==> ./root/.opam
# 2); adding the line: export PATH=$PATH:/root/.opam/bpf/bin
vim /root/.bashrc
source /root/.bashrc
```

# Build dx
```shell
# who: root@8d187e7952ec:/#
# install dx
cd /home/
mkdir CertrBPF
cd CertrBPF/
git clone --branch compcert-3.9 https://gitlab.univ-lille.fr/samuel.hym/dx.git
cd dx
# modify the _CoqProject (adding the second line):
# -R src dx
# -R /root/.opam/bpf/lib/coq-variant/compcert32/compcert compcert
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
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/x86
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/backend
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/debug
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/common
# -I
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cfrontend
vim compcertsrc-I

# adding the following string (removing #) the file `compcertcprinter-cmi`: 
# /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Datatypes.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Nat.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinNums.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinPosDef.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinPos.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zpower.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinNat.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BinInt.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/ZArith_dec.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/List0.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Coqlib.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zbits.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Readconfig.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Responsefile.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Commandline.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver/Configuration.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Archi.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Integers.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zaux.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/SpecFloat.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Zbool.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Round.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/FLT.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Bracket.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Bool.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Binary.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/IEEE754_extra.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Bits.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Floats.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/String0.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/EquivDec.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Maps.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Errors.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/AST.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Values.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Ctypes.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Znumtheory.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Memtype.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/PeanoNat.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Memdata.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Memory.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Cop.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Csyntax.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/lib/Camlcoq.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver/Version.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Diagnostics.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Machine.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Env.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Cprint.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Cutil.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/driver/Clflags.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/common/Sections.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Initializers.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/BoolEqual.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Op.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Machregs.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/backend/Machregsnames.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/x86/Machregsaux.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/Ceval.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/x86/CBuiltins.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cparser/ExtendedAsm.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/debug/Debug.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/extraction/Ctyping.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/backend/AisAnnot.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cfrontend/C2C.cmi /root/.opam/bpf/.opam-switch/build/coq-compcert-32.3.9/cfrontend/PrintCsyntax.cmi 

vim compcertcprinter-cmi

./configure ...
./configure --compcertdir=/root/.opam/bpf/lib/coq-variant/compcert32/compcert --install-compcert-printer --cprinterdir=/root/.opam/bpf/lib/coq/user-contrib/dx/extr
make; make install
# stop and return the following infomation, but it works 
# /bin/sh: 1: tools/modorder: not found
# install: missing destination file operand after '/root/.opam/bpf/lib/coq/user-contrib/dx/extr/compcertcprinter'
# Try 'install --help' for more information.
# make: *** [Makefile:199: install] Error 1

# copy two files
cp cprinter-inc-args /root/.opam/bpf/lib/coq/user-contrib/dx/
cp cprinter-link-args /root/.opam/bpf/lib/coq/user-contrib/dx/
```
# Build CertrBPF
```shell
# who: root@8d187e7952ec:/#
# install CertrBPF
cd ..
git clone --branch CAV22-AE https://gitlab.inria.fr/syuan/rbpf-dx.git
cd rbpf-dx

# modify the file `_CoqProject`:
# -R /home/shyuan/.opam/4.11.1/lib/coq-variant/compcert32/compcert compcert
# ===>
# -R /root/.opam/bpf/lib/coq-variant/compcert32/compcert compcert
vim _CoqProject

# modify the file `Makefile.config` and `verifier/Makefile.config`:
# OPAMPREFIX := /home/shyuan/.opam/4.11.1
# ===>
# OPAMPREFIX := /root/.opam/bpf
vim Makefile.config
vim verifier/Makefile.config

cp /home/CertrBPF/dx/compcertsrc-I .

make all
```
# Test CertrBPF 
```shell
# current folder: /home/CertrBPF/rbpf-dx
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
