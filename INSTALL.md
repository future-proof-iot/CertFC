
# Build world: opam

_NB: you may need to add `sudo` everywhere_

```shell
# assume your ubuntu is named `middleware`
# current folder: /home/middleware/CertrBPF
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
opam switch create bpf ocaml-base-compiler.4.11.1

eval $(opam env)

opam switch list
#   switch  compiler      description
->  bpf     ocaml.4.11.1  bpf

# install coq, compcert-32, etc. NB we need to keep the build directory of compcert-32 by `-b`
opam repository add coq-released https://coq.inria.fr/opam/released

# install coq and coqide
opam install coq.8.13.2 coqide.8.13.2 coq-elpi.1.11.0
```
# Build compcert
There are two ways to install compcert:

1. using opam to install compcert

```
opam install -b coq-compcert-32.3.11
# install cligthgen
opam install coq-vst-32.2.9 # or 2.8
```

2. compile compcert from source code
```
# download source code from https://github.com/AbsInt/CompCert/releases/tag/v3.11
# unzip source code to `YOUR_COMPCERT_DIR` and rename the unzip folder to `compcert` (it is very important!!!)
cd YOUR_COMPCERT_DIR/compcert

# install coq-flocq.4.1.0
opam install coq-flocq.4.1.0
# install 32-bit compcert
./configure arm-linux -use-external-Flocq -clightgen
make all
make clightgen
```

# Build coq2html and set path

```
# install coq2html
git clone https://github.com/xavierleroy/coq2html.git
cd coq2html
make coq2html

# set path variables & add COQPATH
apt-get install vim
# 1) find . -name ".opam" -type d
#  ==> ./home/middleware/.opam
# 2); adding the line: `export PATH=$PATH:/home/middleware/.opam/bpf/bin:/home/middleware/CertrBPF/coq2html`
# 3); adding the line `export COQPATH="$(opam var lib)/coq-variant/compcert32"` when selecting opam to install compcert
#     adding the line `export COQPATH="YOUR_COMPCERT_DIR"` when selecting to install compcert from source code.
#Important: if you recompile CompCert again, remember to comment COQPATH firstly!!!
vim /home/middleware/.bashrc
source /home/middleware/.bashrc
```

# Build dx
```shell
# current folder: /home/middleware/CertrBPF
# install dx
# the current main brach support compcert.3.11 (2022-08-25)
git clone https://gitlab.univ-lille.fr/samuel.hym/dx.git
cd dx
# when using opam to install compcert-32
./configure --cprinterdir="$(opam var lib)/dx" --compcertdir="$(opam var coq-compcert-32:build)" --install-compcert-printer
# when using source code
./configure --cprinterdir="$(opam var lib)/dx" --compcertdir="YOUR_COMPCERT_DIR/compcert" --install-compcert-printer
make all install
```
# Build CertrBPF
```shell
# current folder: /home/middleware/CertrBPF/dx
# install CertrBPF
cd ..
git clone --branch middelware https://github.com/future-proof-iot/CertFC.git
cd CertFC
# when using opam to install compcert
./configure --opamprefixdir=/home/middleware/.opam/bpf
# modify the file `_CoqProject`:
# -R /home/middleware/.opam/bpf/lib/coq-variant/compcert32/compcert compcert
vim _CoqProject

# modify the file `Makefile.config`:
# DXDIR := /home/middleware/.opam/bpf/lib/dx
# COMPCERTDIR := /home/middleware/.opam/bpf/lib/coq-variant/compcert32/compcert
# CLIGHTGEN32DIR := /home/middleware/.opam/bpf/variants/compcert32/bin
# COMPCERTSRCDIR := /home/middleware/.opam/bpf/.opam-switch/build/coq-compcert-32.3.11
vim Makefile.config

# when using source code
./configure --opamprefixdir=/home/middleware/.opam/bpf --compcertdir=YOUR_COMPCERT_DIR/compcert

make all
```
# Test CertrBPF 
```shell
# current folder: /home/middleware/CertrBPF/CertFC
# Here, we only test the native board (*You could reproduce the same result in the paper if you have the same physical boards: Nordic nRF52840 development kit, the Espressif WROOM-32 board, and the Sipeed Longan Nano GD32VF103CBT6 development board*)

# test bench_bpf_coq_incr
# compile CertBPF
make -C benchmark_data/bench_bpf_coq_incr/bpf
make -C benchmark_data/bench_bpf_coq_incr
# run on a native board using CertBPF
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
